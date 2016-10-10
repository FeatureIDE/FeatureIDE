module Arith where
{

  data TypedVal = TVBool Bool;
   
  instance Show TypedVal where
          { show (TVBool b) = show b }
}
