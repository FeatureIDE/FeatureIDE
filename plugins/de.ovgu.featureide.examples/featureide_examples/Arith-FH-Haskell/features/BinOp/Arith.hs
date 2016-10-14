module Arith where
{
  data BinOp = Add
             | Sub
             | Mul
             | Div
             deriving Show;
   
  tvBinOp (Add) (TVString s) (TVString t)
    = Result (TVString (s ++ t));
  tvBinOp (Add) (TVString s) (TVDouble y)
    = Result (TVString (s ++ show y));
  tvBinOp (Add) (TVDouble x) (TVString t)
    = Result (TVString (show x ++ t));
  tvBinOp (Add) (TVDouble x) (TVDouble y)
    = Result (TVDouble (x + y));
  tvBinOp (Sub) (TVDouble x) (TVDouble y)
    = Result (TVDouble (x - y));
  tvBinOp (Mul) (TVDouble x) (TVDouble y)
    = Result (TVDouble (x * y));
  tvBinOp (Div) (TVDouble x) (TVDouble 0) = Fail DivByZero;
  tvBinOp (Div) (TVDouble x) (TVDouble y)
    = Result (TVDouble (x / y));
  tvBinOp _ _ _ = Fail TypeError;
   
  data Exp a = Binary BinOp (Exp a) (Exp a)
             deriving Show;
  
  data EvalError = DivByZero
                 deriving Show
}
