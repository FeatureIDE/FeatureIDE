module CLI where
{ 
  lamExpr :: Parser (Exp TypedVal);
  lamExpr
    = do { reservedOp "\\";
           x <- identifier;
           reservedOp "->";
           e <- expr;
           return (Lam x e)}
        <?> "lambda expression";
   
  appExpr :: Parser (Exp TypedVal);
  appExpr
    = do { es <- many1 appArg;
           return (foldl1 App es)}
        <?> "application";
   
  appArg :: Parser (Exp TypedVal);
  appArg
    = (do { i <- identifier;
            return (Var i)}
         <?> "identifier")
        <|> parens expr
        <|> number
        <|> stringConst
        <|> boolConst
        <?> "argument expression"
}
