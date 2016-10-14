module Arith where
{
  -- In allen Features vorhanden -----------------------------------------------------------
   
  data Result a err = Result a
                    | Fail err
                    deriving Show;
   
  mapResult :: (a -> Result b err) -> Result a err -> Result b err;
  mapResult f (Result x) = f x;
  mapResult f (Fail e) = Fail e;
   
  zipResult ::
              (a -> b -> Result c err) ->
                Result a err -> Result b err -> Result c err;
  zipResult f (Result x) (Result y) = f x y;
  zipResult _ (Fail e) _ = Fail e;
  zipResult _ _ (Fail e) = Fail e;
   
  liftResult :: [Result a err] -> Result [a] err;
  liftResult [] = Result [];
  liftResult (Result x : rest)
    = case liftResult rest of
          { Result xs -> Result (x : xs);
            Fail e -> Fail e};
  liftResult (Fail e : _) = Fail e;

  data Exp a = Const a
             deriving Show;
  
  -- TODO MRO: DivByZero bei BinOps ODER UnOps
  data EvalError = Overflow
                 | TypeError
                 deriving Show;
  
  data TypedVal = TVString String
                | TVDouble Double;
   
  instance Show TypedVal where
          { show (TVString s) = show s; 
            show (TVDouble d) = show d
          }
          

}
