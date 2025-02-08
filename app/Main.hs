{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import UntypedPlutusCore

simplifier ::
  Term DeBruijn DefaultUni DefaultFun () ->
  Term DeBruijn DefaultUni DefaultFun ()
simplifier (Apply () (Apply () (Apply () (Builtin () PLC.IfThenElse) cond) x) y) =
  case PLC.readKnownConstant cond of
    Right cond' -> if cond' then simplifier x else simplifier y
    Left err -> error "no"
simplifier (Apply () (Apply () (Builtin () PLC.AddInteger) x) y) =
  case (PLC.readKnownConstant x, PLC.readKnownConstant y) of
    (Right x', Right y') -> Constant () $ PLC.someValue @Integer (x' + y')
    _ -> error "no"
simplifier (Apply () (Apply () (Builtin () PLC.EqualsInteger) x) y) =
  case (PLC.readKnownConstant @_ @Integer x, PLC.readKnownConstant @_ @Integer y) of
    (Right x', Right y') -> Constant () $ PLC.someValue @Bool (x' == y')
    _ -> error "no"
simplifier org@(Var () v) = org
simplifier (LamAbs () v t) = LamAbs () v (simplifier t)
simplifier org@(Apply () f t) = Apply () (simplifier f) (simplifier t)
simplifier (Force () t) = Force () (simplifier t)
simplifier (Delay () t) = Delay () (simplifier t)
simplifier org@(Constant () val) = org
simplifier org@(Builtin () fun) = org
simplifier org@(Error ()) = org
simplifier (Constr () idx ts) = Constr () idx (simplifier <$> ts)
simplifier (Case () t ts) = Case () (simplifier t) (simplifier <$> ts)

test :: Term DeBruijn DefaultUni DefaultFun ()
test =
  Apply
    ()
    ( Apply
        ()
        ( Apply
            ()
            (Builtin () PLC.IfThenElse)
            (Constant () $ PLC.someValue False)
        )
        (Var () (DeBruijn 0))
    )
    (Var () (DeBruijn 1))

testa :: Term DeBruijn DefaultUni DefaultFun ()
testa =
  Apply
    ()
    ( Apply
        ()
        ( Apply
            ()
            (Builtin () PLC.IfThenElse)
            (Constant () $ PLC.someValue False)
        )
        (Var () (DeBruijn 42))
    )
    (Var () (DeBruijn 69))

test' :: Term DeBruijn DefaultUni DefaultFun ()
test' =
  Apply
    ()
    ( Apply
        ()
        ( Apply
            ()
            (Builtin () PLC.IfThenElse)
            (Constant () $ PLC.someValue False)
        )
        testa
    )
    (Apply () (Apply () (Builtin () PLC.EqualsInteger) (Constant () (PLC.someValue @Integer 10))) (Constant () (PLC.someValue @Integer 10)))

-- $> import UntypedPlutusCore; import PlutusCore qualified as PLC; import Main

-- $> :t PLC.IfThenElse

-- $> test'

-- $> simplifier test'

main :: IO ()
main = pure ()
