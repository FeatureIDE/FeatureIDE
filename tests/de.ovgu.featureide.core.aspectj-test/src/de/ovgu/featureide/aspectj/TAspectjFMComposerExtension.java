package de.ovgu.featureide.aspectj;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

/**
 * Tests for AspectJ renaming;
 * 
 * @author Jens Meinicke
 */
public class TAspectjFMComposerExtension {
	private AspectJFMCompserExtension fmComposerExtension = new AspectJFMCompserExtension();
	
	private static final String CONTENT_1 = 
			"public aspect Hello{\r\n" +
			"before(): call(void Main.print()) {\r\n" +
			"	System.out.print(\"Hello\");\r\n" +
			"	}\r\n" +
			"}";
	private static final Object NEW_CONTENT_1 = 
			"public aspect NewAspect{\r\n" +
			"before(): call(void Main.print()) {\r\n" +
			"	System.out.print(\"Hello\");\r\n" +
			"	}\r\n" +
			"}";
	
	private static final String OLD_NAME_1_1 = "Hello";
	private static final String NEW_NAME_1 = "NewAspect";

	@Test
	public void performRenamingsTest_1_1() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_1, OLD_NAME_1_1, NEW_NAME_1, true), NEW_CONTENT_1);
	}
	
	private static final String OLD_NAME_1_2 = "Hell";
	
	@Test
	public void performRenamingsTest_1_2() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_1, OLD_NAME_1_2, NEW_NAME_1, true), CONTENT_1);
	}
	
	private static final String CONTENT_2 = 
			"abstract aspect AbstractLogger {\r\n" +
			"declare precedence: AbstractLogger, PrintLogger, SetLogger;\r\n" +
			"	abstract pointcut loggingPointcut();\r\n" +
			"	PrintStream loggingTarget = System.out;\r\n" +
			"	protected void log(String logStr) {\r\n" +
			"	loggingTarget.println(logStr);\r\n" +
			"	}\r\n" +
			"	after() : loggingPointcut() {\r\n" +
			"	log('Join point reached ' + thisJoinPoint);\r\n" +
			"	}\r\n" +
			"}\r\n" +
			"aspect PrintLogger extends AbstractLogger {\r\n" +
			"	pointcut loggingPointcut() : execution(* print*(..));\r\n" +
			"}\r\n" +
			"aspect SetLogger extends AbstractLogger {\r\n" +
			"	pointcut loggingPointcut() : execution(* set*(..));\r\n" +
			"	protected voidlog(String logStr) {\r\n" +
			"	super.log('Set Method: ' + logStr);\r\n" +
			"	}\r\n" +
			"}";
	
	private static final String CONTENT_2_1 = 
			"abstract aspect ALogger {\r\n" +
			"declare precedence: ALogger, PrintLogger, SetLogger;\r\n" +
			"	abstract pointcut loggingPointcut();\r\n" +
			"	PrintStream loggingTarget = System.out;\r\n" +
			"	protected void log(String logStr) {\r\n" +
			"	loggingTarget.println(logStr);\r\n" +
			"	}\r\n" +
			"	after() : loggingPointcut() {\r\n" +
			"	log('Join point reached ' + thisJoinPoint);\r\n" +
			"	}\r\n" +
			"}\r\n" +
			"aspect PrintLogger extends ALogger {\r\n" +
			"	pointcut loggingPointcut() : execution(* print*(..));\r\n" +
			"}\r\n" +
			"aspect SetLogger extends ALogger {\r\n" +
			"	pointcut loggingPointcut() : execution(* set*(..));\r\n" +
			"	protected voidlog(String logStr) {\r\n" +
			"	super.log('Set Method: ' + logStr);\r\n" +
			"	}\r\n" +
			"}";
	
	private static final String OLD_NAME_2_1 = "AbstractLogger";
	private static final String NEW_NAME_2_1 = "ALogger";
	
	@Test
	public void performRenamingsTest_2_1() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_2, OLD_NAME_2_1, NEW_NAME_2_1, true), CONTENT_2_1);
	}
	
	private static final String CONTENT_2_2 = 
			"abstract aspect AbstractLogger {\r\n" +
			"declare precedence: AbstractLogger, PLogger, SetLogger;\r\n" +
			"	abstract pointcut loggingPointcut();\r\n" +
			"	PrintStream loggingTarget = System.out;\r\n" +
			"	protected void log(String logStr) {\r\n" +
			"	loggingTarget.println(logStr);\r\n" +
			"	}\r\n" +
			"	after() : loggingPointcut() {\r\n" +
			"	log('Join point reached ' + thisJoinPoint);\r\n" +
			"	}\r\n" +
			"}\r\n" +
			"aspect PLogger extends AbstractLogger {\r\n" +
			"	pointcut loggingPointcut() : execution(* print*(..));\r\n" +
			"}\r\n" +
			"aspect SetLogger extends AbstractLogger {\r\n" +
			"	pointcut loggingPointcut() : execution(* set*(..));\r\n" +
			"	protected voidlog(String logStr) {\r\n" +
			"	super.log('Set Method: ' + logStr);\r\n" +
			"	}\r\n" +
			"}";
	
	private static final String OLD_NAME_2_2 = "PrintLogger";
	private static final String NEW_NAME_2_2 = "PLogger";
	
	@Test
	public void performRenamingsTest_2_2() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_2, OLD_NAME_2_2, NEW_NAME_2_2, true), CONTENT_2_2);
	}
	
	private static final String CONTENT_2_3 = 
			"abstract aspect AbstractLogger {\r\n" +
			"declare precedence: AbstractLogger, PrintLogger, SLogger;\r\n" +
			"	abstract pointcut loggingPointcut();\r\n" +
			"	PrintStream loggingTarget = System.out;\r\n" +
			"	protected void log(String logStr) {\r\n" +
			"	loggingTarget.println(logStr);\r\n" +
			"	}\r\n" +
			"	after() : loggingPointcut() {\r\n" +
			"	log('Join point reached ' + thisJoinPoint);\r\n" +
			"	}\r\n" +
			"}\r\n" +
			"aspect PrintLogger extends AbstractLogger {\r\n" +
			"	pointcut loggingPointcut() : execution(* print*(..));\r\n" +
			"}\r\n" +
			"aspect SLogger extends AbstractLogger {\r\n" +
			"	pointcut loggingPointcut() : execution(* set*(..));\r\n" +
			"	protected voidlog(String logStr) {\r\n" +
			"	super.log('Set Method: ' + logStr);\r\n" +
			"	}\r\n" +
			"}";
	
	private static final String OLD_NAME_2_3 = "SetLogger";
	private static final String NEW_NAME_2_3 = "SLogger";
	
	@Test
	public void performRenamingsTest_2_3() {
		assertEquals(fmComposerExtension.changeFileContent(CONTENT_2, OLD_NAME_2_3, NEW_NAME_2_3, true), CONTENT_2_3);
	}

}
