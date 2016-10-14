module Arith where
{
  data UnOp = Not
            deriving Show;
            
  tvUnOp (Not) (TVBool x) = Result (TVBool (not x))
}
