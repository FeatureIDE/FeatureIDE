package de.fosd.typechef;

import static de.ovgu.featureide.fm.core.localization.StringTable.FILE_HAS_CONTRADICTORY_PRESENCE_CONDITION__EXISTING_;

import java.io.File;

import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.models.RenderParserError;
import br.ufal.ic.colligens.models.RenderTypeError;
import de.fosd.typechef.Frontend.StopWatch;
import de.fosd.typechef.crewrite.CIntraAnalysisFrontend;
import de.fosd.typechef.featureexpr.FeatureModel;
import de.fosd.typechef.options.FrontendOptions;
import de.fosd.typechef.parser.TokenReader;
import de.fosd.typechef.parser.c.AST;
import de.fosd.typechef.parser.c.CParser;
import de.fosd.typechef.parser.c.CToken;
import de.fosd.typechef.parser.c.CTypeContext;
import de.fosd.typechef.parser.c.ParserMain;
import de.fosd.typechef.parser.c.TranslationUnit;
import de.fosd.typechef.typesystem.CTypeSystemFrontend;
import de.fosd.typechef.typesystem.linker.CInterface;

public final class TypeChefFrontend {

	// public void processFile(FrontendOptions opt, FileProxy fileProxy) {
	//
	// RenderParserError renderParserError = new RenderParserError();
	// renderParserError.setFile(fileProxy);
	//
	// opt.setRenderParserError((Function3<FeatureExpr, String, Position,
	// Object>) renderParserError);
	//
	// Frontend.StopWatch stopWatch = new Frontend.StopWatch();
	// stopWatch.start("loadFM");
	//
	// FeatureModel fm = opt.getFeatureModel().and(opt.getLocalFeatureModel())
	// .and(opt.getFilePresenceCondition());
	// opt.setFeatureModel(fm);
	// if (opt.getFilePresenceCondition().isSatisfiable(fm)) {
	// stopWatch.start("lexing");
	// TokenReader<CToken, CTypeContext> in = lex(opt);
	//
	// if (opt.parse) {
	// stopWatch.start("parsing");
	//
	// ParserMain parserMain = new ParserMain(new CParser(fm, false));
	// AST ast = parserMain.parserMain(in, opt);
	//
	// stopWatch.start("serialize");
	// if ((ast != null) && (opt.serializeAST)) {
	// // serializeAST(ast, opt.getSerializedASTFilename());
	// }
	// if (ast != null) {
	// FeatureModel fm_ts = opt.getFeatureModelTypeSystem()
	// .and(opt.getLocalFeatureModel())
	// .and(opt.getFilePresenceCondition());
	// CTypeSystemFrontend ts = new CTypeSystemFrontend(
	// (TranslationUnit) ast, fm_ts);
	//
	// if (opt.typecheck) {
	// stopWatch.start("typechecking");
	// System.out.println("type checking.");
	// ts.checkAST();
	//
	// RenderTypeError renderTypeError = new RenderTypeError();
	// renderTypeError.setFile(fileProxy);
	// ts.errors().mapConserve(renderTypeError);
	// }
	// if (opt.writeInterface) {
	// // stopWatch.start("interfaces");
	// // CInterface interface =
	// //
	// ts.getInferredInterface(ts.getInferredInterface$default$1()).and(opt.getFilePresenceCondition());
	// //
	// // stopWatch.start("writeInterfaces");
	// // ts.writeInterface(interface, new
	// // File(opt.getInterfaceFilename()));
	// // if (opt.writeDebugInterface)
	// // ts.debugInterface(interface, new
	// // File(opt.getDebugInterfaceFilename()));
	// }
	// if (opt.conditionalControlFlow) {
	// stopWatch.start("controlFlow");
	//
	// CAnalysisFrontend cf = new CAnalysisFrontend(
	// (TranslationUnit) ast, fm_ts);
	// cf.checkCfG();
	// }
	// if (opt.dataFlow) {
	// stopWatch.start("dataFlow");
	// ProductGeneration.dataflowAnalysis(
	// fm_ts,
	// ast,
	// opt,
	// new StringBuilder()
	// .append("Time for lexing(ms): ")
	// .append(BoxesRunTime
	// .boxToLong(stopWatch
	// .get("lexing")))
	// .append("\nTime for parsing(ms): ")
	// .append(BoxesRunTime
	// .boxToLong(stopWatch
	// .get("parsing")))
	// .append("\n").toString());
	// }
	// }
	//
	// }
	//
	// stopWatch.start("done");
	// if (opt.recordTiming)
	// System.out
	// .println(new StringBuilder()
	// .append("timing (lexer, parser, type system, interface inference, conditional control flow, data flow)\n")
	// .append(BoxesRunTime.boxToLong(stopWatch
	// .get("lexing")))
	// .append(";")
	// .append(BoxesRunTime.boxToLong(stopWatch
	// .get("parsing")))
	// .append(";")
	// .append(BoxesRunTime.boxToLong(stopWatch
	// .get("typechecking")))
	// .append(";")
	// .append(BoxesRunTime.boxToLong(stopWatch
	// .get("interfaces")))
	// .append(";")
	// .append(BoxesRunTime.boxToLong(stopWatch
	// .get("controlFlow")))
	// .append(";")
	// .append(BoxesRunTime.boxToLong(stopWatch
	// .get("dataFlow"))).toString());
	// } else {
	// System.out
	// .println(FILE_HAS_CONTRADICTORY_PRESENCE_CONDITION__EXISTING_);
	// }
	// }

	public void processFile(FrontendOptions opt, FileProxy fileProxy) {

		final RenderParserError renderParserError = new RenderParserError();
		renderParserError.setFile(fileProxy);

		opt.setRenderParserError(renderParserError);

		final StopWatch stopWatch = new StopWatch();
		stopWatch.start("loadFM");

		final FeatureModel fm = opt.getLexerFeatureModel().and(opt.getLocalFeatureModel()).and(opt.getFilePresenceCondition());
		opt.setFeatureModel(fm);// otherwise the lexer does not get the updated
								// feature model with file presence conditions
		if (!opt.getFilePresenceCondition().isSatisfiable(fm)) {
			System.out.println(FILE_HAS_CONTRADICTORY_PRESENCE_CONDITION__EXISTING_); // otherwise
																						 // this
																						 // can
																						 // lead
																						 // to
																						 // strange
																						 // parser
																						 // errors,
																						 // because
																						 // True
																						 // is
																						 // satisfiable,
																						 // but
																						 // anything
																						 // else
																						 // isn't
			return;
		}

		AST ast = null;
		if (opt.reuseAST && opt.parse && new File(opt.getSerializedASTFilename()).exists()) {
			System.out.println("loading AST.");
			try {
				ast = Frontend.loadSerializedAST(opt.getSerializedASTFilename());
				ast = Frontend.prepareAST(ast);
			} catch (final Throwable e) {
				System.out.println(e.toString());
				e.printStackTrace();
				ast = null;
			}
			if (ast == null) {
				System.out.println("... failed reading AST\n");
			}
		}

		stopWatch.start("lexing");
		// no parsing if read serialized ast
		TokenReader<CToken, CTypeContext> in = null;
		if (ast == null) {
			in = Frontend.lex(opt);
		}

		if (opt.parse) {
			stopWatch.start("parsing");

			if (ast == null) {
				// no parsing and serialization if read serialized ast
				final ParserMain parserMain = new ParserMain(new CParser(fm, false));
				ast = parserMain.parserMain(in, opt);

				if (ast == null) {
					return;
				}
				ast = Frontend.prepareAST(ast);

				if ((ast != null) && opt.serializeAST) {
					stopWatch.start("serialize");
					Frontend.serializeAST(ast, opt.getSerializedASTFilename());
				}

			}

			if (ast != null) {
				final FeatureModel fm_ts = opt.getTypeSystemFeatureModel().and(opt.getLocalFeatureModel()).and(opt.getFilePresenceCondition());

				// some dataflow analyses require typing information
				final CTypeSystemFrontend ts = new CTypeSystemFrontend((TranslationUnit) ast, fm_ts, opt);

				/**
				 * I did some experiments with the TypeChef FeatureModel of Linux, in case I need the routines again, they are saved here.
				 */
				// Debug_FeatureModelExperiments.experiment(fm_ts)

				if (opt.typecheck || opt.writeInterface || opt.typechecksa()) {
					// ProductGeneration.typecheckProducts(fm,fm_ts,ast,opt,
					// logMessage=("Time for lexing(ms): " + (t2-t1) +
					// "\nTime for parsing(ms): " + (t3-t2) + "\n"))
					// ProductGeneration.estimateNumberOfVariants(ast, fm_ts)

					stopWatch.start("typechecking");
					System.out.println("type checking.");
					ts.checkAST(ts.checkAST$default$1());
					final RenderTypeError renderTypeError = new RenderTypeError();
					renderTypeError.setFile(fileProxy);
					ts.errors().mapConserve(renderTypeError);
				}
				if (opt.writeInterface) {
					stopWatch.start("interfaces");
					final CInterface cinterface =
						ts.getInferredInterface(ts.getInferredInterface$default$1(), ts.getInferredInterface$default$2()).and(opt.getFilePresenceCondition());
					stopWatch.start("writeInterfaces");
					ts.writeInterface(cinterface, new File(opt.getInterfaceFilename()));
					if (opt.writeDebugInterface) {
						ts.debugInterface(cinterface, new File(opt.getDebugInterfaceFilename()));
					}
				}
				if (opt.dumpcfg) {
					stopWatch.start("dumpCFG");

					// CInterAnalysisFrontend cf = new
					// CInterAnalysisFrontend(ast, fm_ts);
					// CFGCSVWriter writer = new CFGCSVWriter(new FileWriter(new
					// File(opt.getCCFGFilename())));
					// DotGraph dotwriter = new DotGraph(new FileWriter(new
					// File(opt.getCCFGDotFilename())));
					// cf.writeCFG(opt.getFile(), new
					// ComposedWriter(List.apply(Predef..wrapRefArray((Object[])new
					// IOUtilities[] { dotwriter, writer }))));
				}

				if (opt.staticanalyses()) {
					final CIntraAnalysisFrontend sa = new CIntraAnalysisFrontend((TranslationUnit) ast, ts, fm_ts);
					if (opt.warning_double_free()) {
						stopWatch.start("doublefree");
						sa.doubleFree();
					}
					if (opt.warning_uninitialized_memory()) {
						stopWatch.start("uninitializedmemory");
						sa.uninitializedMemory();
					}
					if (opt.warning_case_termination()) {
						stopWatch.start("casetermination");
						sa.caseTermination();
					}
					if (opt.warning_xfree()) {
						stopWatch.start("xfree");
						sa.xfree();
					}
					if (opt.warning_dangling_switch_code()) {
						stopWatch.start("danglingswitchcode");
						sa.danglingSwitchCode();
					}
					if (opt.warning_cfg_in_non_void_func()) {
						stopWatch.start("cfginnonvoidfunc");
						sa.cfgInNonVoidFunc();
					}
					if (opt.warning_stdlib_func_return()) {
						stopWatch.start("checkstdlibfuncreturn");
						sa.stdLibFuncReturn();
					}
					if (opt.warning_dead_store()) {
						stopWatch.start("deadstore");
						sa.deadStore();
					}
				}

			}

		}
		stopWatch.start("done");
		if (opt.recordTiming) {
			System.out.println(stopWatch);
		}
	}
}
