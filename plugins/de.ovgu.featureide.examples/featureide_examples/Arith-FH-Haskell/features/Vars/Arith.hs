module Arith where
{
 -- Vars
  eval env (Var name)
    = case lookupEnv env name of
          { Just x -> Result x;
            Nothing -> Fail UndefVarError};
  eval _ (Const x) = Result x;
   
  evalExp :: Exp TypedVal -> Result TypedVal EvalError;
  evalExp exp = eval emptyEnv exp;   
   
  lookupEnv :: Env a -> String -> Maybe a;
  lookupEnv (Env env) name = lookup name env;
   
  emptyEnv :: Env a;
  emptyEnv = Env [];
   
  addToEnv :: Env a -> String -> a -> Env a;
  addToEnv (Env env) name val = Env ((name, val) : env);
   
  addToEnvN :: Env a -> [(String, a)] -> Env a;
  addToEnvN (Env env) newdefs = Env (newdefs ++ env);
   
  data Exp a = Var String						-- Vars
             | Let [(String, Exp a)] (Exp a)	-- Vars
             deriving Show;
  
  -- TODO MRO: DivByZero bei BinOps ODER UnOps
  data EvalError = UndefVarError				-- Vars
                 deriving Show;

  data Env a = Env [(String, a)]
             deriving Show
}
