{-# LANGUAGE ViewPatterns #-}

module Main (main) where

{-
I'm going to use UPLC with DeBruijn index. This is the codebase I'll be working on, so why not use this?
To better demonstrate my skills, I'll refrain from using utilities from `plutus-core`.
-}
import Control.Monad (void)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word64)
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Error qualified as PLC
import Prettyprinter
import Test.Tasty
import Test.Tasty.HUnit
import UntypedPlutusCore
import UntypedPlutusCore.Parser

newtype Or = Or {unOr :: Bool}

instance Semigroup Or where
  x <> y = Or $ unOr x || unOr y

instance Monoid Or where
  mempty = Or False

-- Very convenient
termFromText :: Text -> Term DeBruijn DefaultUni DefaultFun ()
termFromText str =
  case PLC.runQuoteT $ parseTerm @PLC.ParserErrorBundle str of
    Right x ->
      case deBruijnTerm @FreeVariableError x of
        Right y -> void $ termMapNames unNameDeBruijn y
        Left err -> error (show err)
    Left err -> error (show err)

{- |
@applyTopLam@ applies provide argument to a body of lambda abstraction. Noticeably, this function does few things:
- Run down through AST and change any @Var@ constructor that binds to abstraction we are applying to.
  This is obvious, it's actual application part.
- Adjust free @Var@s to have correct indices for variables in function.
  Since application means we are taking out one abstraction(the one we are applying to), any free variables that bind to
  "outside" abstraction need have their indices reduced by one.
- Adjust free @Var@s to have correctly shifted indices for variables in argument.
  When we inline argument, any free variables in the argument must be adjusted as the location of in-lining can be
  inside of other abstractions. So, we just add "depth" of abstraction to any free variables within argument.

In addition, we also re-calculate DeBruijn level here. This is to reduce number of times we need to iterate AST.
-}
applyTopLam ::
  Term DeBruijn DefaultUni DefaultFun () ->
  ((Or, [Integer]), Term DeBruijn DefaultUni DefaultFun ()) ->
  ((Or, [Integer]), Term DeBruijn DefaultUni DefaultFun ())
applyTopLam target ((argEffectful, argUsed), arg) = subst' 0 target
  where
    -- Increment the free variables by given amount, leave bound variables unchanged.
    -- Some of the utilities from UntypedPlutusCore can be used here, but I implemented everything from scratch.
    incrementTerm ::
      Word64 ->
      Word64 ->
      Term DeBruijn DefaultUni DefaultFun () ->
      Term DeBruijn DefaultUni DefaultFun ()
    incrementTerm d incrAmount org@(Var () (DeBruijn (Index idx)))
      | idx <= d = org
      | otherwise = Var () (DeBruijn (Index $ idx + incrAmount))
    incrementTerm d incrAmount (LamAbs () v t) = LamAbs () v (incrementTerm (d + 1) incrAmount t)
    incrementTerm d incrAmount (Apply () f t) = Apply () (incrementTerm d incrAmount f) (incrementTerm d incrAmount t)
    incrementTerm d incrAmount (Force () t) = Force () (incrementTerm d incrAmount t)
    incrementTerm d incrAmount (Delay () t) = Delay () (incrementTerm d incrAmount t)
    incrementTerm d incrAmount (Constr () idx ts) = Constr () idx (incrementTerm d incrAmount <$> ts)
    incrementTerm d incrAmount (Case () t ts) =
      Case () (incrementTerm d incrAmount t) (incrementTerm d incrAmount <$> ts)
    incrementTerm _ _ x = x

    -- argument @d@ tracks the "depth" of abstractions. When we face @LamAbs@, this will be incremented.
    subst' :: Integer -> Term DeBruijn DefaultUni DefaultFun () -> ((Or, [Integer]), Term DeBruijn DefaultUni DefaultFun ())
    subst' d x@(Var () (DeBruijn (Index (toInteger -> n)))) =
      case compare (n - d) 1 of
        -- This is the target variable we want to apply to. Since this is being inlined, we need to increment
        -- the indices of the free variables by @d@.
        -- Also, we subtract $d$ from each of DeBruijn level as now it's displaced further by amount @d@.
        EQ -> ((argEffectful, (- d) <$> argUsed), incrementTerm 0 (fromInteger d) arg)
        -- We don't need to change variable if it's bounded and not the target variable
        LT -> ((Or False, [1 - n]), x)
        -- We need to decrement index by one if it's free variable.
        GT -> ((Or False, [1 - (n - 1)]), Var () (DeBruijn (Index $ fromInteger $ n - 1)))
    subst' d (LamAbs () v t) = let ((effectful, used'), t') = subst' (d + 1) t in ((effectful, (+ 1) <$> used'), LamAbs () v t')
    subst' d (Apply () f t) = Apply () <$> subst' d f <*> subst' d t
    subst' d (Force () t) = Force () <$> subst' d t
    subst' d (Delay () t) = Delay () <$> subst' d t
    subst' d (Constr () idx ts) = Constr () idx <$> traverse (subst' d) ts
    subst' d (Case () t ts) = Case () <$> subst' d t <*> traverse (subst' d) ts
    subst' _ org@(Builtin _ _) = ((Or True, mempty), org)
    subst' _ org@(Error _) = ((Or True, mempty), org)
    subst' _ org@(Constant _ _) = ((Or False, mempty), org)

{- |
This is the actual simplify function. I tried to make it do minimal traversal of AST.
Currently, it will only traverse each node once provided that given term is fully simplified.

Unfortunately, it will be more complicated to make @simplify@ traverse AST nodes once when simplifications(specifically beta
reduction) are possible. This is mainly due to the fact that we need to first know rather or not beta-reduction can be done,
so we need to traverse to see if there's zero or one bind first and than do substitution.

I do have some fun ideas regarding making this more efficient, but for the sake of simplicity, I will proceed with this.

Limitations and deficiency of this implementation can be found at the bottom of this file.
-}
simplify :: Term DeBruijn DefaultUni DefaultFun () -> Term DeBruijn DefaultUni DefaultFun ()
simplify = snd . go
  where
    -- @go@ returns list of all variables in DeBruijn level and simplified term.
    -- We will use this list of DeBruijn level to count number of variable used in the body of abstraction.
    -- DeBruijn level assigns 1 to the outer most abstraction, so when we run @go@ on the body of abstraction
    -- and we can count number of @0@ to see how many times the corresponding variable is used.
    go :: Term DeBruijn DefaultUni DefaultFun () -> ((Or, [Integer]), Term DeBruijn DefaultUni DefaultFun ())
    -- Handle integer addition and equality, nothing special here. If given constant is of incorrect type,
    -- don't do anything and keep original.
    go org@(Apply () (Apply () (Builtin () PLC.AddInteger) x) y) = do
      (,) <$> go x <*> go y >>= \case
        (x'@(Constant _ _), y'@(Constant _ _)) ->
          case (PLC.readKnownConstant x', PLC.readKnownConstant y') of
            (Right x'', Right y'') -> ((Or False, mempty), Constant () $ PLC.someValue @Integer (x'' + y''))
            _ -> ((Or True, mempty), org)
        (x', y') -> pure (Apply () (Apply () (Builtin () PLC.AddInteger) x') y')
    go org@(Apply () (Apply () (Builtin () PLC.EqualsInteger) x) y) =
      (,) <$> go x <*> go y >>= \case
        (x'@(Constant _ _), y'@(Constant _ _)) ->
          case (PLC.readKnownConstant @_ @Integer x', PLC.readKnownConstant @_ @Integer y') of
            (Right x'', Right y'') -> ((Or False, mempty), Constant () $ PLC.someValue @Bool (x'' == y''))
            _ -> ((Or True, mempty), org)
        (x', y') -> pure (Apply () (Apply () (Builtin () PLC.EqualsInteger) x') y')
    -- Handle IfThenElse. Mostly similar with integer addition/equality. But for this one, we want
    -- to also simplify each cases of IfThenElse.
    go (Apply () (Apply () (Apply () (Builtin () PLC.IfThenElse) cond@(Constant _ _)) x) y) =
      case PLC.readKnownConstant cond of
        Right cond' ->
          if cond'
            then go x
            else go y
        _ -> do
          -- We only need to take DeBruijn levels from both branches when we can't simplify IfThenElse.
          x' <- go x
          y' <- go y
          pure (Apply () (Apply () (Apply () (Builtin () PLC.IfThenElse) cond) x') y')

    -- Beta-reduction for variable that's only been used zero or one time.
    go (Apply () (LamAbs () v f) arg) =
      let
        -- We use @lamUsed@ here to check number of times the variable bound to current abstraction is used.
        ((lamEffectful, lamUsed), lamSimplified) = go f
        argBoth@((argEffectful, argUsed), argSimplified) = go arg
       in
        -- Only reduce when variable is used zero or one time.
        case argSimplified of
          -- When argument is constant, always reduce.
          c@(Constant _ _) ->
            -- Here we discard @_lamUsed@ because @applyTopLam@ recalculates DeBruijn level.
            let ((_, _lamUsed), lamSimplified) = go f
             in -- no need to modify index of variable being applied since it is outside of abstraction
                -- This should be @applyTopLam (snd $ go f) (mempty, c)@ but I wrote it out for better clarity
                applyTopLam lamSimplified (mempty, c)
          -- When argument is variable, always reduce.
          v@(Var _ (DeBruijn (Index i))) ->
            let ((_, _lamUsed), lamSimplified) = go f
             in applyTopLam lamSimplified ((Or False, [1 - toInteger i]), v)
          _ ->
            if length (filter (== 0) lamUsed) == 1 || (0 `notElem` lamUsed && not (unOr argEffectful))
              then applyTopLam lamSimplified argBoth
              else -- Here, we increment each elements of @lamUsed@ since no reduction was performed.
                ((lamEffectful <> argEffectful, ((+ 1) <$> lamUsed) <> argUsed), Apply () (LamAbs () v lamSimplified) argSimplified)
    -- BeBruijn level starts from @1 - v@ and on each encounter of abstraction, they get incremented.
    -- Variables that binds to first abstraction will get level 1, second will get 2 and so on.
    -- First free variable gets level 0. Hence, when finding "target" variable on the abstraction body,
    -- we can just count number of zeros.
    go org@(Var () (DeBruijn (Index v))) = ((Or False, [1 - toInteger v]), org)
    go (LamAbs () v t) = let ((effectful, used'), t') = go t in ((effectful, (+ 1) <$> used'), LamAbs () v t')
    -- Handles applications, function and argument needs to be simplified as well.
    -- We also check if function gets reduced into an abstraction, in which case we want to attempt to
    -- simplify once more. This is so that functions like @[[(lam x x) (lam x x)] [(lam x x) (lam x x)]]@
    -- correctly gets fully simplified.
    go (Apply () f t) =
      let
        (usedf, f') = go f
        (usedt, t') = go t
       in
        case f' of
          (LamAbs {}) -> go (Apply () f' t')
          _ -> (usedf <> usedt, Apply () f' t')
    -- Nothing interesting here.
    go (Force () t) = Force () <$> go t
    go (Delay () t) = Delay () <$> go t
    go org@(Constant _ _) = ((Or False, mempty), org)
    go org@(Builtin _ _) = ((Or True, mempty), org)
    go org@(Error ()) = ((Or True, mempty), org)
    -- It is possible to do further optimization on SOP terms. Namely reducing @(case (constr 1 ...) a b c)@
    -- to @b ...@. This should be somewhat trivial.
    go (Constr () idx ts) = Constr () idx <$> traverse go ts
    go (Case () t ts) = Case () <$> go t <*> traverse go ts

-- I will not make a futile attempt to write out some property testing here. However, if I were to implement it, I would
-- generate arbitrary term(call it @t@) and argument(call it @x@) to check @eval (t x) == eval (simplify t $ x)@.
-- Generating proper arbitrary UPLC will be very difficult. So, instead, here are some tests:

simplifiesTo :: Text -> Text -> TestTree
simplifiesTo x y = testCase (T.unpack $ x <> " simplifies to " <> y) $ do
  simplify (termFromText x) @?= termFromText y

simplifiesTo' :: Term DeBruijn DefaultUni DefaultFun () -> Term DeBruijn DefaultUni DefaultFun () -> TestTree
simplifiesTo' x y = testCase (show $ pretty x <> " simplifies to " <> pretty y) $ do
  simplify x @?= y

tests :: TestTree
tests =
  testGroup
    "Simplifier"
    [ -- Beta reductions
      simplifiesTo "[[(lam x x) (lam x x)] [(lam x x) (lam x x)]]" "(lam x x)"
    , simplifiesTo "(lam a (lam b [(lam x [(lam y y) x]) [a b]]))" "(lam x (lam y [x y]))"
    , simplifiesTo "(lam a (lam b [(lam c c) [a b]]))" "(lam c (lam d [c d]))"
    , -- simplify builtin equalsInteger when both arguments are constant integers
      simplifiesTo "[(builtin equalsInteger) (con integer 20) (con integer 30)]" "(con bool False)"
    , -- simplify builtin equalsInteger when both arguments are constant integers, nested
      simplifiesTo
        "[(builtin equalsInteger) [(lam x x) (con integer 20)] (con integer 30)]"
        "(con bool False)"
    , -- remain unchanged when both arguments are not constant integers
      simplifiesTo
        "[(builtin equalsInteger) (con bool True) (con integer 30)]"
        "[(builtin equalsInteger) (con bool True) (con integer 30)]"
    , simplifiesTo
        "(lam x [(builtin equalsInteger) [x (con integer 20)] (con integer 30)])"
        "(lam x [(builtin equalsInteger) [x (con integer 20)] (con integer 30)])"
    , -- remain unchanged when both arguments are not constant integers, nested
      simplifiesTo
        "(lam x [(builtin equalsInteger) [(lam y y) x] (con integer 30)])"
        "(lam x [(builtin equalsInteger) x (con integer 30)])"
    , -- simplify builtin addInteger when both arguments are constant integers
      simplifiesTo "[(builtin addInteger) (con integer 20) (con integer 30)]" "(con integer 50)"
    , -- simplify builtin addInteger when both arguments are constant integers, nested
      simplifiesTo
        "[(builtin addInteger) [(lam x x) (con integer 20)] (con integer 30)]"
        "(con integer 50)"
    , -- remain unchanged when both arguments are not constant integers
      simplifiesTo
        "[(builtin addInteger) (con bool False) (con integer 30)]"
        "[(builtin addInteger) (con bool False) (con integer 30)]"
    , simplifiesTo
        "(lam x [(builtin addInteger) [x (con bool False)] (con integer 30)])"
        "(lam x [(builtin addInteger) [x (con bool False)] (con integer 30)])"
    , -- remain unchanged when both arguments are not constant integers, nested
      simplifiesTo
        "(lam x [(builtin addInteger) [(lam y y) x] (con integer 30)])"
        "(lam x [(builtin addInteger) x (con integer 30)])"
    , -- constant argument always get reduced
      simplifiesTo "[(lam x [x x]) (con integer 42)]" "[(con integer 42) (con integer 42)]"
    , simplifiesTo "[(lam x [x x x]) (con integer 42)]" "[(con integer 42) (con integer 42) (con integer 42)]"
    , -- variable argument always get reduced
      simplifiesTo "(lam y [(lam x [x x]) y])" "(lam y [y y])"
    , simplifiesTo "(lam y [(lam x [x x x]) y])" "(lam y [y y y])"
    , -- argument that is not variable nor constant will only get reduced if they occur zero or once.
      simplifiesTo "(lam a (lam b [(lam x x) [a b]]))" "(lam a (lam b [a b]))"
    , simplifiesTo "(lam a (lam b [(lam x [x x]) [a b]]))" "(lam a (lam b [(lam x [x x]) [a b]]))"
    , -- argument will get simplified first in nested cases.
      simplifiesTo
        "(lam a (lam b [(lam x [x x]) [(builtin addInteger) (con integer 10) (con integer 20)]]))"
        "(lam a (lam b [(con integer 30) (con integer 30)]))"
    , -- free variables arguments can still be reduced
      simplifiesTo'
        (Apply () (LamAbs () (DeBruijn 0) (Var () (DeBruijn 1))) (Var () (DeBruijn 3)))
        (Var () (DeBruijn 3))
    , simplifiesTo'
        (Apply () (LamAbs () (DeBruijn 0) (Apply () (Var () (DeBruijn 1)) (Var () (DeBruijn 1)))) (Var () (DeBruijn 2)))
        (Apply () (Var () (DeBruijn 2)) (Var () (DeBruijn 2)))
    , -- Now this is safe and well.
      simplifiesTo
        "[(lam a (con integer 30)) (error)]"
        "[(lam a (con integer 30)) (error)]"
    , -- Now this is safe and well.
      simplifiesTo
        "[(lam a a) (error)]"
        "(error)"
    ]

{-
Okay, I can pull together more cases, but it's rather laborious. So, instead, I leveraged Plutarch's 864 test cases
to see if @simplifer@ does anything stupid and also to see if anything actually gets optimized:
https://github.com/Plutonomicon/plutarch-plutus/compare/staging...seungheonoh/simplifierExperiment
Upon inspecting the diffs in benchmark goldens, you will be able to observe pretty significant optimizations.

There are few deficiency(pretty critical ones in fact) in this simplify if we were to use this in actual UPLC:

Firstly, for UPLC specifically, with @Error@ term making it somewhat effectful, truncating unused argument
(via beta-reduction) is dangerous. As of now, @simplify@ implies all terms to be "pure", so it will simplify
@[(lam a (con integer 30)) (error)]@ to @(con integer 30)@ which we don't want for very clear reasons. This can be fixed
rather easily. I will demonstrate this in "seungheonoh/handleEffectfulTerm" branch.

Secondly, beta-reducing arguments that is only being used once doesn't always guarantee performance improvement; especially
with regards to execution units. Consider example in pseudocode:
@@
bob = (\y -> (\x -> add (replicate 100 x)) (y + y + y + y + y))

simplify bob => (\y -> add (replicate 100 (y + y + y + y + y)))
@@
In this case @bob@ is more efficient than @simplify bob@ in terms of execution unit(of CEK machine). Simplified @bob@
will extraneously repeat computation of @y + y + y + y + y@ 100 times which original @bob@ prevented by having abstraction.
This is difficult to detect; some sort of static analysis would be required to determine when and when not to reduce. I won't
demonstrate if this can be done or not as it is significant undertaking. However, my intuition suggests me that this would be
better feasible in more abstracted IR(like plutus-ir or covenant) where recursion is handled at IR level.
-}

main :: IO ()
main = defaultMain tests

-- ghcid

-- $> main
