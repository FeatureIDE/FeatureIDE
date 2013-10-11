package de.fosd.typechef;

import scala.Function3;
import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.models.RenderParserError;
import br.ufal.ic.colligens.models.RenderTypeError;
import de.fosd.typechef.Frontend.StopWatch;
import de.fosd.typechef.featureexpr.FeatureExpr;
import de.fosd.typechef.parser.Position;
import de.fosd.typechef.parser.c.AST;
import de.fosd.typechef.parser.c.CParser;
import de.fosd.typechef.parser.c.ParserMain;
import de.fosd.typechef.parser.c.TranslationUnit;
import de.fosd.typechef.typesystem.CTypeSystemFrontend;

public class FrontendTypeChef {
	public void processFile(FrontendOptions opt, FileProxy fileProxy) {

		RenderParserError renderParserError = new RenderParserError();
		renderParserError.setFile(fileProxy);

		opt.setRenderParserError((Function3<FeatureExpr, String, Position, Object>) renderParserError);

		StopWatch stopWatch = new StopWatch();
		stopWatch.start("loadFM");

		opt.setFeatureModel(opt.getFeatureModel()
				.and(opt.getLocalFeatureModel())
				.and(opt.getFilePresenceCondition()));
		// otherwise the lexer does not get the updated feature model with file
		// presence conditions

		stopWatch.start("lexing");
		// val in = Frontend.lex(opt);

		if (opt.parse) {
			stopWatch.start("parsing");

			ParserMain parserMain = new ParserMain(new CParser(
					opt.getFeatureModel(), false));
			AST ast = parserMain.parserMain(Frontend.lex(opt), opt);

			stopWatch.start("serialize");
			if (ast != null && opt.serializeAST)
				Frontend.serializeAST(ast, opt.getSerializedASTFilename());

			if (ast != null) {

				CTypeSystemFrontend ts = new CTypeSystemFrontend(
						(TranslationUnit) ast, opt.getFeatureModelTypeSystem()
								.and(opt.getLocalFeatureModel())
								.and(opt.getFilePresenceCondition()));

				/**
				 * I did some experiments with the TypeChef FeatureModel of
				 * Linux, in case I need the routines again, they are saved
				 * here.
				 */
				// Debug_FeatureModelExperiments.experiment(fm_ts)

				if (opt.typecheck || opt.writeInterface) {
					// ProductGeneration.typecheckProducts(fm,fm_ts,ast,opt,
					// logMessage=("Time for lexing(ms): " + (t2-t1) +
					// "\nTime for parsing(ms): " + (t3-t2) + "\n"))
					// ProductGeneration.estimateNumberOfVariants(ast, fm_ts)

					stopWatch.start("typechecking");
					// println("type checking.");
					ts.checkAST();

					 RenderTypeError renderTypeError = new RenderTypeError(
					 ts.errors());
					 
					 renderTypeError.setFile(fileProxy);
					 renderTypeError.run();
					 
				}
				if (opt.writeInterface) {
					// stopWatch.start("interfaces");
					// val interface =
					// ts.getInferredInterface().and(opt.getFilePresenceCondition);
					//
					// stopWatch.start("writeInterfaces");
					// ts.writeInterface(interface, new
					// File(opt.getInterfaceFilename));
					// if (opt.writeDebugInterface)
					// ts.debugInterface(interface, new
					// File(opt.getDebugInterfaceFilename));
				}
				if (opt.conditionalControlFlow) {
					// stopWatch.start("controlFlow");
					//
					// val cf = new
					// CAnalysisFrontend(ast.asInstanceOf[TranslationUnit],
					// fm_ts);
					// cf.checkCfG();
				}
				if (opt.dataFlow) {
					// stopWatch.start("dataFlow");
					// ProductGeneration.dataflowAnalysis(fm_ts, ast, opt,
					// logMessage = ("Time for lexing(ms): " +
					// (stopWatch.get("lexing")) + "\nTime for parsing(ms): " +
					// (stopWatch.get("parsing")) + "\n"))
				}

			}

		}
		stopWatch.start("done");

	}

	public void renderParserError(FeatureExpr r, String string,
			Position position, Object object) {
		System.err.println(string);
	}
}
