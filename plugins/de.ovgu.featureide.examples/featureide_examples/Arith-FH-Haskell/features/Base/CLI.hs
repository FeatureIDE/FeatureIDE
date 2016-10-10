module CLI where
{ import Control.Exception ( catch, SomeException );
  import System.IO;
  import Text.ParserCombinators.Parsec;
  import Text.ParserCombinators.Parsec.Expr;
  import Text.ParserCombinators.Parsec.Language;
  import qualified Text.ParserCombinators.Parsec.Token as PT;
  import Arith;
  
  lexer :: PT.TokenParser ();
  lexer
    = PT.makeTokenParser
        (haskellDef{reservedNames = ["let", "in", "ite", "true", "false"],
        						-- TODO MRO: - bei BinOps ODER UnOps
                    reservedOpNames = ["+", "-", "*", "/", "&&", "||", "#", "!", "\\", "=", "->"]});
  reserved = PT.reserved lexer;
  reservedOp = PT.reservedOp lexer;
  parens = PT.parens lexer;
  semi = PT.semi lexer;
  identifier = PT.identifier lexer;
  naturalOrFloat = PT.naturalOrFloat lexer;
  stringLiteral = PT.stringLiteral lexer;
   
  expr :: Parser (Exp TypedVal);
  expr = buildExpressionParser table factor <?> "expression";
  
  -- TODO MRO: f�rben
  factor :: Parser (Exp TypedVal);
  factor
    =   do { reservedOp "-";
           e <- expr;
           return (Unary Neg e)}
        <|>
        do { reservedOp "#";
             e <- expr;
             return (Unary Recip e)}
        <|>
        do { reservedOp "!";
             e <- expr;
             return (Unary Not e)}
        <|> letExpr
        <|> lamExpr
        <|> iteExpr
        <|> appExpr
        <?> "simple expression";
   
  number :: Parser (Exp TypedVal);
  number
    = do { nof <- naturalOrFloat;
           case nof of
               { Right d -> return (Const (TVDouble d));
                 Left n -> return (Const (TVDouble (fromIntegral n)))}}
        <?> "number";
   
  stringConst :: Parser (Exp TypedVal);
  stringConst
    = do { s <- stringLiteral;
           return (Const (TVString s))}
        <?> "string literal"
}
