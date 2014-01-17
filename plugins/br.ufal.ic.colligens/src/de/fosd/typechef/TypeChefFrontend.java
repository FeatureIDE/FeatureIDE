package de.fosd.typechef;

import java.util.List;

import scala.Function3;
import scala.runtime.BoxesRunTime;
import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.models.RenderParserError;
import br.ufal.ic.colligens.models.RenderTypeError;
import de.fosd.typechef.crewrite.CAnalysisFrontend;
import de.fosd.typechef.featureexpr.FeatureExpr;
import de.fosd.typechef.featureexpr.FeatureModel;
import de.fosd.typechef.lexer.Main;
import de.fosd.typechef.parser.Position;
import de.fosd.typechef.parser.TokenReader;
import de.fosd.typechef.parser.c.AST;
import de.fosd.typechef.parser.c.CLexer;
import de.fosd.typechef.parser.c.CParser;
import de.fosd.typechef.parser.c.CToken;
import de.fosd.typechef.parser.c.CTypeContext;
import de.fosd.typechef.parser.c.ParserMain;
import de.fosd.typechef.parser.c.TranslationUnit;
import de.fosd.typechef.typesystem.CTypeSystemFrontend;

public final class TypeChefFrontend {

	public void processFile(FrontendOptions opt, FileProxy fileProxy) {

		RenderParserError renderParserError = new RenderParserError();
		renderParserError.setFile(fileProxy);

		opt.setRenderParserError((Function3<FeatureExpr, String, Position, Object>) renderParserError);

		Frontend.StopWatch stopWatch = new Frontend.StopWatch();
		stopWatch.start("loadFM");

		FeatureModel fm = opt.getFeatureModel().and(opt.getLocalFeatureModel())
				.and(opt.getFilePresenceCondition());
		opt.setFeatureModel(fm);
		if (opt.getFilePresenceCondition().isSatisfiable(fm)) {
			stopWatch.start("lexing");
			TokenReader<CToken, CTypeContext> in = lex(opt);

			if (opt.parse) {
				stopWatch.start("parsing");

				ParserMain parserMain = new ParserMain(new CParser(fm, false));
				AST ast = parserMain.parserMain(in, opt);

				stopWatch.start("serialize");
				if ((ast != null) && (opt.serializeAST)) {
					// serializeAST(ast, opt.getSerializedASTFilename());
				}
				if (ast != null) {
					FeatureModel fm_ts = opt.getFeatureModelTypeSystem()
							.and(opt.getLocalFeatureModel())
							.and(opt.getFilePresenceCondition());
					CTypeSystemFrontend ts = new CTypeSystemFrontend(
							(TranslationUnit) ast, fm_ts);

					if (opt.typecheck) {
						stopWatch.start("typechecking");
						System.out.println("type checking.");
						ts.checkAST();

						RenderTypeError renderTypeError = new RenderTypeError();
						renderTypeError.setFile(fileProxy);
						ts.errors().mapConserve(renderTypeError);
					}
					if (opt.writeInterface) {
						// stopWatch.start("interfaces");
						// CInterface interface =
						// ts.getInferredInterface(ts.getInferredInterface$default$1()).and(opt.getFilePresenceCondition());
						//
						// stopWatch.start("writeInterfaces");
						// ts.writeInterface(interface, new
						// File(opt.getInterfaceFilename()));
						// if (opt.writeDebugInterface)
						// ts.debugInterface(interface, new
						// File(opt.getDebugInterfaceFilename()));
					}
					if (opt.conditionalControlFlow) {
						stopWatch.start("controlFlow");

						CAnalysisFrontend cf = new CAnalysisFrontend(
								(TranslationUnit) ast, fm_ts);
						cf.checkCfG();
					}
					if (opt.dataFlow) {
						stopWatch.start("dataFlow");
						ProductGeneration.dataflowAnalysis(
								fm_ts,
								ast,
								opt,
								new StringBuilder()
										.append("Time for lexing(ms): ")
										.append(BoxesRunTime
												.boxToLong(stopWatch
														.get("lexing")))
										.append("\nTime for parsing(ms): ")
										.append(BoxesRunTime
												.boxToLong(stopWatch
														.get("parsing")))
										.append("\n").toString());
					}
				}

			}

			stopWatch.start("done");
			if (opt.recordTiming)
				System.out
						.println(new StringBuilder()
								.append("timing (lexer, parser, type system, interface inference, conditional control flow, data flow)\n")
								.append(BoxesRunTime.boxToLong(stopWatch
										.get("lexing")))
								.append(";")
								.append(BoxesRunTime.boxToLong(stopWatch
										.get("parsing")))
								.append(";")
								.append(BoxesRunTime.boxToLong(stopWatch
										.get("typechecking")))
								.append(";")
								.append(BoxesRunTime.boxToLong(stopWatch
										.get("interfaces")))
								.append(";")
								.append(BoxesRunTime.boxToLong(stopWatch
										.get("controlFlow")))
								.append(";")
								.append(BoxesRunTime.boxToLong(stopWatch
										.get("dataFlow"))).toString());
		} else {
			System.out
					.println("file has contradictory presence condition. existing.");
		}
	}

	public TokenReader<CToken, CTypeContext> lex(FrontendOptions opt) {
		List<LexerToken> tokens;
		try {
			tokens = (List<LexerToken>) new Main().run(opt, opt.parse);
			TokenReader<CToken, CTypeContext> in = CLexer.prepareTokens(tokens);

			return in;
		} catch (Exception e) {
			
			e.printStackTrace();
		}
		return null;
	}
}