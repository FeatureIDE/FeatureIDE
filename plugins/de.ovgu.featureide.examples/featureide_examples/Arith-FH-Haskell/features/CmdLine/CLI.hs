module CLI where
{
 
--
-- Command line loop
--
loop :: IO ();
loop = do {
		  putStr "> ";
          l <- getLine;
          case Just l of {
             Nothing -> return ();
             Just "" -> return ();
             Just ll ->
                 do {Control.Exception.catch
                       (putStrLn $ parseAndEval ll)
                       (\e -> print (e :: SomeException));
                     loop}
          }
          }
    where {
    	parseAndEval str =
        	case parse parser "" str of {
            	Left  pe  -> show pe;
            	Right res -> show $ evalExp res
        	};
    	parser = do { e <- expr; eof; return e }
   	};

main :: IO ();
main = do { hSetBuffering stdout NoBuffering;
          putStrLn "Simple command line interpreter. Exit with empty input.";
          loop
          }
}
