module CLI where
{  
  letExpr :: Parser (Exp TypedVal);
  letExpr
    = do { reserved "let";
           ds <- sepBy decl semi;
           reserved "in";
           e <- expr;
           return (Let ds e)}
        <?> "let expression";
   
  decl :: Parser (String, Exp TypedVal);
  decl
    = do { x <- identifier;
           reservedOp "=";
           e <- expr;
           return (x, e)}
        <?> "variable binding"
   
}
