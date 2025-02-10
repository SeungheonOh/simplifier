{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Main (main, applyTopLam, simplifya) where

import Control.Monad (void)
import Control.Monad.Cont
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word64)
import Debug.Trace
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Error qualified as PLC
import Prettyprinter
import Test.Tasty
import Test.Tasty.HUnit
import UntypedPlutusCore
import UntypedPlutusCore.Parser

termFromText :: Text -> Term DeBruijn DefaultUni DefaultFun ()
termFromText str =
  case PLC.runQuoteT $ parseTerm @PLC.ParserErrorBundle str of
    Right x ->
      case deBruijnTerm @FreeVariableError x of
        Right y -> void $ termMapNames unNameDeBruijn y
        Left err -> error (show err)
    Left err -> error (show err)

applyTopLam ::
  Term DeBruijn DefaultUni DefaultFun () ->
  ([Integer], Term DeBruijn DefaultUni DefaultFun ()) ->
  ([Integer], Term DeBruijn DefaultUni DefaultFun ())
applyTopLam target (argUsed, arg) = subst' 0 target
  where
    incrementTerm :: Word64 -> Word64 -> Term DeBruijn DefaultUni DefaultFun () -> Term DeBruijn DefaultUni DefaultFun ()
    incrementTerm d incrAmount org@(Var () (DeBruijn (Index idx)))
      | idx <= d = org
      | otherwise = Var () (DeBruijn (Index $ idx + incrAmount))
    incrementTerm d incrAmount (LamAbs () v t) = LamAbs () v (incrementTerm (d + 1) incrAmount t)
    incrementTerm d incrAmount (Apply () f t) = Apply () (incrementTerm d incrAmount f) (incrementTerm d incrAmount t)
    incrementTerm d incrAmount (Force () t) = Force () (incrementTerm d incrAmount t)
    incrementTerm d incrAmount (Delay () t) = Delay () (incrementTerm d incrAmount t)
    incrementTerm d incrAmount (Constr () idx ts) = Constr () idx (incrementTerm d incrAmount <$> ts)
    incrementTerm d incrAmount (Case () t ts) = Case () (incrementTerm d incrAmount t) (incrementTerm d incrAmount <$> ts)
    incrementTerm _ _ x = x

    subst' :: Integer -> Term DeBruijn DefaultUni DefaultFun () -> ([Integer], Term DeBruijn DefaultUni DefaultFun ())
    subst' d x@(Var () (DeBruijn (Index (toInteger -> n)))) =
      case compare (n - d) 1 of
        EQ -> ((- d) <$> argUsed, incrementTerm 0 (fromInteger d) arg)
        LT -> ([1 - n], x)
        GT -> ([1 - (n - 1)], Var () (DeBruijn (Index $ fromInteger $ n - 1)))
    subst' d (LamAbs () v t) = let (used', t') = subst' (d + 1) t in ((+ 1) <$> used', LamAbs () v t')
    subst' d (Apply () f t) = Apply () <$> subst' d f <*> subst' d t
    subst' d (Force () t) = Force () <$> subst' d t
    subst' d (Delay () t) = Delay () <$> subst' d t
    subst' d (Constr () idx ts) = Constr () idx <$> traverse (subst' d) ts
    subst' d (Case () t ts) = Case () <$> subst' d t <*> traverse (subst' d) ts
    subst' _ x = (mempty, x)

--   simplifiesTo "[[(lam x x) (lam x x)] [(lam x x) (lam x x)]]" "(lam x x)"
-- , simplifiesTo "(lam a (lam b [(lam x [(lam y y) x]) [a b]]))" "(lam x (lam y [x y]))"

-- $> pretty $ simplifya $ termFromText "(lam a (lam b [(lam x [(lam y y) x]) [a b]]))"

-- $> pretty $ simplifya $ termFromText "(lam a (lam b [(lam x x) a]))"

simplifya :: Term DeBruijn DefaultUni DefaultFun () -> Term DeBruijn DefaultUni DefaultFun ()
simplifya x = snd $ runCont (go 0 x) (\(d, v) -> ([d - v + 1], Var () (DeBruijn $ Index $ fromInteger v)))
  where
    go ::
      Integer ->
      Term DeBruijn DefaultUni DefaultFun () ->
      Cont ([Integer], Term DeBruijn DefaultUni DefaultFun ()) (Integer, Integer)
    go d org@(Apply () (Apply () (Builtin () PLC.AddInteger) x) y) = cont $ \r ->
      (,) <$> runCont (go d x) r <*> runCont (go d y) r >>= \case
        (x'@(Constant _ _), y'@(Constant _ _)) ->
          case (PLC.readKnownConstant x', PLC.readKnownConstant y') of
            (Right x'', Right y'') -> (mempty, Constant () $ PLC.someValue @Integer (x'' + y''))
            _ -> (mempty, org)
        (x', y') -> pure (Apply () (Apply () (Builtin () PLC.AddInteger) x') y')
    go d org@(Apply () (Apply () (Builtin () PLC.EqualsInteger) x) y) = cont $ \r ->
      (,) <$> runCont (go d x) r <*> runCont (go d y) r >>= \case
        (x'@(Constant _ _), y'@(Constant _ _)) ->
          case (PLC.readKnownConstant @_ @Integer x', PLC.readKnownConstant @_ @Integer y') of
            (Right x'', Right y'') -> (mempty, Constant () $ PLC.someValue @Bool (x'' == y''))
            _ -> (mempty, org)
        (x', y') -> pure (Apply () (Apply () (Builtin () PLC.EqualsInteger) x') y')
    go d (Apply () (Apply () (Apply () (Builtin () PLC.IfThenElse) cond@(Constant _ _)) x) y) = cont $ \r ->
      case PLC.readKnownConstant cond of
        Right cond' ->
          if cond'
            then runCont (go d x) r
            else runCont (go d y) r
        _ -> do
          x' <- runCont (go d x) r
          y' <- runCont (go d y) r
          pure (Apply () (Apply () (Apply () (Builtin () PLC.IfThenElse) cond) x') y')
    go d org@(Apply () (LamAbs () v lam) arg) = cont $ \r ->
      let
        lam' = go d lam
        arg' = go d arg
        updateArg incr (d', v')
          | d' - d < v' = r (d', v' + incr)
          | otherwise = r (d', v')
        apply (d', v')
          | (d' - d) == v' - 1 = runCont arg' (updateArg $ d' - d)
          | (d' - d) < v' - 1 = r (d', v' - 1)
          | otherwise = r (d' - 1, v')
       in
        case snd $ runCont arg' r of
          c@(Constant _ _) -> runCont lam' apply
          v@(Var _ (DeBruijn (Index i))) -> runCont lam' apply
          _ ->
            if length (filter (== d) (fst $ runCont lam' r)) <= 1
              then runCont lam' apply
              else Apply () <$> (LamAbs () v <$> runCont lam' (\(x, y) -> r (x + 1, y))) <*> runCont arg' r
    go d (Var () (DeBruijn (Index (toInteger -> v)))) = cont (\f -> f (d, v))
    go d (LamAbs () v t) = cont (fmap (LamAbs () v) . runCont (go (d + 1) t))
    go d (Apply () f t) = cont $ \r -> do
      f' <- runCont (go d f) r
      t' <- runCont (go d t) r
      case f' of
        LamAbs {} -> runCont (go d (Apply () f' t')) r
        _ -> pure $ Apply () f' t'
    go d (Force () t) = cont (fmap (Force ()) . runCont (go d t))
    go d (Delay () t) = cont (fmap (Delay ()) . runCont (go d t))
    go d org@(Constant _ _) = cont $ const (mempty, org)
    go d org@(Builtin _ _) = cont $ const (mempty, org)
    go d org@(Error ()) = cont $ const (mempty, org)
    go d (Constr () idx ts) =
      cont (\r -> Constr () idx <$> traverse (flip runCont r . go d) ts)
    go d (Case () t ts) =
      cont (\r -> Case () <$> runCont (go d t) r <*> traverse (flip runCont r . go d) ts)

simplify :: Term DeBruijn DefaultUni DefaultFun () -> Term DeBruijn DefaultUni DefaultFun ()
simplify = snd . simplify'

simplify' :: Term DeBruijn DefaultUni DefaultFun () -> ([Integer], Term DeBruijn DefaultUni DefaultFun ())
simplify' = go
  where
    go :: Term DeBruijn DefaultUni DefaultFun () -> ([Integer], Term DeBruijn DefaultUni DefaultFun ())
    go org@(Apply () (Apply () (Builtin () PLC.AddInteger) x) y) = do
      (,) <$> go x <*> go y >>= \case
        (x'@(Constant _ _), y'@(Constant _ _)) ->
          case (PLC.readKnownConstant x', PLC.readKnownConstant y') of
            (Right x'', Right y'') -> (mempty, Constant () $ PLC.someValue @Integer (x'' + y''))
            _ -> (mempty, org)
        (x', y') -> pure (Apply () (Apply () (Builtin () PLC.AddInteger) x') y')
    go org@(Apply () (Apply () (Builtin () PLC.EqualsInteger) x) y) =
      (,) <$> go x <*> go y >>= \case
        (x'@(Constant _ _), y'@(Constant _ _)) ->
          case (PLC.readKnownConstant @_ @Integer x', PLC.readKnownConstant @_ @Integer y') of
            (Right x'', Right y'') -> (mempty, Constant () $ PLC.someValue @Bool (x'' == y''))
            _ -> (mempty, org)
        (x', y') -> pure (Apply () (Apply () (Builtin () PLC.EqualsInteger) x') y')
    go (Apply () (Apply () (Apply () (Builtin () PLC.IfThenElse) cond@(Constant _ _)) x) y) =
      case PLC.readKnownConstant cond of
        Right cond' ->
          if cond'
            then go x
            else go y
        _ -> do
          x' <- go x
          y' <- go y
          pure (Apply () (Apply () (Apply () (Builtin () PLC.IfThenElse) cond) x') y')
    go (Apply () (LamAbs () v f) arg) =
      let
        (lamUsed, lamSimplified) = go f
        argBoth@(argUsed, argSimplified) = go arg
       in
        case argSimplified of
          c@(Constant _ _) ->
            let (_lamUsed, lamSimplified) = go f
             in applyTopLam lamSimplified (mempty, c)
          v@(Var _ (DeBruijn (Index i))) ->
            let (_lamUsed, lamSimplified) = go f
             in applyTopLam lamSimplified ([1 - toInteger i], v)
          _ ->
            if length (filter (== 0) lamUsed) <= 1
              then applyTopLam lamSimplified argBoth
              else (((+ 1) <$> lamUsed) <> argUsed, Apply () (LamAbs () v lamSimplified) argSimplified)
    go org@(Var () (DeBruijn (Index v))) = ([1 - toInteger v], org)
    go (LamAbs () v t) = let (used', t') = go t in ((+ 1) <$> used', LamAbs () v t')
    go (Apply () f t) =
      let
        (usedf, f') = go f
        (usedt, t') = go t
       in
        case f' of
          (LamAbs {}) -> go (Apply () f' t')
          _ -> (usedf <> usedt, Apply () f' t')
    go (Force () t) = Force () <$> go t
    go (Delay () t) = Delay () <$> go t
    go org@(Constant _ _) = (mempty, org)
    go org@(Builtin _ _) = (mempty, org)
    go org@(Error ()) = (mempty, org)
    go (Constr () idx ts) = Constr () idx <$> traverse go ts
    go (Case () t ts) = Case () <$> go t <*> traverse go ts

simplifiesTo :: Text -> Text -> TestTree
simplifiesTo x y = testCase (T.unpack $ x <> " simplifies to " <> y) $ do
  simplifya (termFromText x) @?= termFromText y

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
    , -- Dangerous
      simplifiesTo
        "[(lam a (con integer 30)) (error)]"
        "(con integer 30)"
    ]

{-
Okay, I can pull together more cases, but it's rather laborious. So, instead, I leveraged Plutarch's 864 test cases
to see if @simplifer@ does anything stupid and also to see if anything actually gets optimized:
https://github.com/Plutonomicon/plutarch-plutus/compare/staging...seungheonoh/simplifierExperiment
Upon inspecting the diffs in benchmark goldens, you will be able to observe pretty significant optimizations.

There are few deficiency(pretty critical ones in fact) in this @simplify@ if we were to use this in actual UPLC:

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
