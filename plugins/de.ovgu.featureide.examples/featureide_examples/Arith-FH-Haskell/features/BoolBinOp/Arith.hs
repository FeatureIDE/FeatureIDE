module Arith where
{
  data BinOp = And
             | Or
             deriving Show;
   
  tvBinOp (And) (TVBool x) (TVBool y)
    = Result (TVBool (x && y));
  tvBinOp (Or) (TVBool x) (TVBool y)
    = Result (TVBool (x || y))
}
