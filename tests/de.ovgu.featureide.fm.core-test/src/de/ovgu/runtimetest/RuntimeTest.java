/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.runtimetest;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintStream;
import java.lang.annotation.Annotation;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import org.junit.Assert;
import org.junit.Test;

import de.ovgu.runtimetest.RuntimeTest.Logger.Level;

/**
 * A runtime test extends JUnit capabilities by defining additional acceptance ranges for <i>timeout</i> tests. Instead of giving a fixed <i>timeout</i> value,
 * the tester defines an optional minimum (<b>allowedMinus</b>) and an optional maximum (<b>allowedPlus</b>) allowed variation of a given run time that is
 * compared to previous runs. If a method runtime is outside this range, the test will fail. To implement a test, the user have to inherent a class from the
 * abstract base class <code>RuntimeTest</code> but there is no need to specify additional <code>@Test</code> annotations of JUnit. To invoke runtime
 * constraints on certain methods, a <b>@Constraint</b> annotation is required. Inside this annotation, it is required to specify a maximum sample count
 * (<b>samples</b>) and the optional minimum and maximum ranges.
 *
 * <br/><br/> <b>Note</b>: Since JUnit invokes a starter method inside this class, the entire test will stop if at least one method under test fail by
 * constraint violation or regular exceptions or assertions. An additional JUnit <code>@Test</code> annotation will lead to an additional test drive by JUnit
 * but with regular behavior.
 *
 * <br/><br/> <b>Example</b> <pre><code> import java.util.Random;
 *
 * public class MyTest extends RuntimeTest {
 *
 * static { disableThisTest = false; historyLength = HistoryLength.FIVE_ENTRIES; logger = Logger.LOG_NOTHING; }
 *
 * @Annotations.WarmUp public void methodBeforeTesting() { // Add code here }
 *
 *
 * @Annotations.CoolDown public void methodAfterTesting() { // Add code here }
 *
 *
 * @Annotations.Constraint(samples=5,allowedPlus=3) public void foo1() throws InterruptedException { Thread.sleep(new Random().nextInt(20)); }
 *
 * @Annotations.Constraint(samples=5,allowedPlus=10,allowedMinus=1) public void foo2() throws InterruptedException { Thread.sleep(new Random().nextInt(10)); } }
 *                                                                  </code></pre>
 *
 * @author Marcus Pinnecke (pinnecke@ovgu.de)
 *
 */
public abstract class RuntimeTest {

	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	//
	// A N N O T A T I O N S
	//
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	/**
	 * Annotation namespace
	 *
	 * @author Marcus Pinnecke (pinnecke@ovgu.de)
	 */
	public static class Annotations {

		/**
		 * Specifies that a user-defined method should be automatically invoked and tested in terms of regular JUnit/Java behavior and runtime behavior.
		 *
		 * @see WarmUp
		 * @see CoolDown
		 *
		 * @author Marcus Pinnecke (pinnecke@ovgu.de)
		 */
		@Target(value = ElementType.METHOD)
		@Retention(value = RetentionPolicy.RUNTIME)
		public @interface Constraint {

			double allowedMinus() default Double.NEGATIVE_INFINITY;

			double allowedPlus() default Double.POSITIVE_INFINITY;

			int samples();
		}

		/**
		 * Methods annotated with this annotation will be executed before the first invocation of <code>@Constraint</code> methods.
		 *
		 * @see WarmUp
		 * @see Constraint
		 *
		 * @author Marcus Pinnecke (pinnecke@ovgu.de)
		 */
		@Target(value = ElementType.METHOD)
		@Retention(value = RetentionPolicy.RUNTIME)
		public @interface CoolDown {}

		/**
		 * Methods annotated with this annotation will be executed after the last invocation of <code>@Constraint</code> methods.
		 *
		 * @see CoolDown
		 * @see Constraint
		 *
		 * @author Marcus Pinnecke (pinnecke@ovgu.de)
		 */
		@Target(value = ElementType.METHOD)
		@Retention(value = RetentionPolicy.RUNTIME)
		public @interface WarmUp {}
	}

	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	//
	// E X C E P T I O N S
	//
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	class RangeException extends RuntimeException {

		private static final long serialVersionUID = 5567220675749347664L;

		public RangeException(final Annotations.Constraint constraint) {
			super("Constraint ranges for test are out of bounds or negative. Lower bound = method runtime - " + (-constraint.allowedMinus())
				+ ", upper bound = method runtime + " + constraint.allowedPlus()
				+ "]. Lower bound must be less method runtime and upper bound must be greater than runtime.");
		}
	}

	class ViolationException extends AssertionError {

		private static final long serialVersionUID = 7877278129859302108L;

		public ViolationException(final String msg) {
			super(msg);
		}
	}

	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	//
	// H I S T O R Y
	//
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	public static abstract class History {

		public static class PlainTextFileHistory extends History {

			protected String directoryToStoreFiles;

			protected final String fileExtension;

			public PlainTextFileHistory(final Logger logger, final String directoryToStoreFiles, final String fileExtension) {
				super(logger);
				if (!new File(directoryToStoreFiles).isDirectory()) {
					throw new RuntimeException(String.format("\"%s\" is not a accessible directory", directoryToStoreFiles));
				} else {
					this.directoryToStoreFiles = directoryToStoreFiles;
					this.fileExtension = fileExtension;
				}
			}

			private File clear(File file) {
				assert (file != null);

				if (file.exists()) {
					file.delete();
				}

				assert (!file.exists());
				return file;
			}

			@Override
			protected void clearHistory(final String clazz, final String method) {
				assert ((clazz != null) && !clazz.isEmpty());
				assert ((method != null) && !method.isEmpty());

				clear(new File(autoName(clazz, method)));

				assert (!new File(autoName(clazz, method)).exists());
			}

			@Override
			protected boolean hasHistory(final String clazz, final String method) {
				assert ((clazz != null) && !clazz.isEmpty());
				assert ((method != null) && !method.isEmpty());

				return new File(autoName(clazz, method)).exists();
			}

			@Override
			protected Queue<Double> loadHistory(final String clazz, final String method) {
				assert ((clazz != null) && !clazz.isEmpty());
				assert ((method != null) && !method.isEmpty());

				final Queue<Double> retval = new LinkedList<>();
				try {
					for (final String s : readAllLines(Paths.get(autoName(clazz, method)))) {
						retval.add(Double.valueOf(s));
					}
				} catch (final Exception e) {
					Assert.fail("Unable to load: " + autoName(clazz, method));
				}

				return retval;
			}

			private String autoName(final String clazz, final String method) {
				assert ((clazz != null) && !clazz.isEmpty());
				assert ((method != null) && !method.isEmpty());
				return clazz + "_" + method + "." + fileExtension;
			}

			@Override
			protected void storeHistory(String clazz, String method, Collection<Double> runtimes) {
				assert ((clazz != null) && !clazz.isEmpty());
				assert ((method != null) && !method.isEmpty());
				assert (runtimes != null);

				final File file = clear(new File(autoName(clazz, method)));
				try (final PrintStream ps = new PrintStream(file)) {
					for (final Double d : runtimes) {
						ps.println(d);
					}
				} catch (final FileNotFoundException e) {
					e.printStackTrace();
				}
			}
		}

		public static class Result {

			public static final Result PASSES = new Result(true, "");

			String message;

			boolean testPass = false;

			public Result(final boolean pass, final String msg) {
				testPass = pass;
				message = msg;
			}
		}

		protected static Logger logger;

		protected final Map<String, Map<String, Queue<Double>>> history = new HashMap<>();

		public History(final Logger logger) {
			History.logger = logger;
		}

		private boolean valid(final Class<? extends RuntimeTest> clazz, final Method method, final Queue<Double> runtimes,
				final Annotations.Constraint constraint, final double avgRuntime) {
			assert (clazz != null);
			assert (method != null);
			assert ((runtimes != null) && !runtimes.isEmpty());
			assert (constraint != null);

			final double recordedAvg = avg(runtimes);
			final double max = constraint.allowedPlus() == Double.POSITIVE_INFINITY ? constraint.allowedMinus() : recordedAvg + constraint.allowedPlus();
			final double min = constraint.allowedMinus() == Double.NEGATIVE_INFINITY ? constraint.allowedMinus() : recordedAvg - constraint.allowedMinus();

			assert (recordedAvg >= 0);
			assert (max >= recordedAvg);
			assert (min <= recordedAvg);

			final boolean pass = ((min == Double.NEGATIVE_INFINITY) || (avgRuntime >= min)) && ((max == Double.POSITIVE_INFINITY) || (avgRuntime <= max));

			logger.logLn(Level.DEBUG, method.getName() + " average from history: " + recordedAvg + "msec");
			logger.logLn(Level.DEBUG,
					"\tActual processing duration: " + avgRuntime + "msec in [" + min + ", " + max + "]" + (pass ? "...[PASSED]" : "...[FAILED]"));

			return pass;
		}

		protected abstract void clearHistory(final String clazz, final String method);

		protected abstract boolean hasHistory(final String clazz, final String method);

		public Result addRun(final HistoryLength historyConfig, final Class<? extends RuntimeTest> clazz, final Method method,
				final Annotations.Constraint constraint, final double avgRuntime) {
			assert (clazz != null);
			assert (method != null);
			assert (constraint != null);
			assert (avgRuntime >= 0);

			final Map<String, Queue<Double>> methodRuntimes = getOrDefault(history, clazz.getName(), new HashMap<String, Queue<Double>>());
			final Queue<Double> runtimes = getOrDefault(methodRuntimes, method.getName(),
					hasHistory(clazz.getName(), method.getName()) ? loadHistory(clazz.getName(), method.getName()) : new LinkedList<Double>());
			if (historyConfig.maximumEntries > 0) {
				if (!runtimes.isEmpty() && !valid(clazz, method, runtimes, constraint, avgRuntime)) {
					final double recordedAvg = avg(runtimes);
					final double max = recordedAvg + constraint.allowedPlus();
					final double min = recordedAvg - constraint.allowedMinus();
					return new Result(false, makeMessage(avgRuntime, min, max, clazz, method));
				} else {
					runtimes.add(avgRuntime);
				}
			}
			cleanUp(runtimes, historyConfig);
			clearHistory(clazz.getName(), method.getName());
			storeHistory(clazz.getName(), method.getName(), runtimes);

			assert (runtimes.size() <= historyConfig.maximumEntries);
			return Result.PASSES;
		}

		private String makeMessage(final double avg, final double min, final double max, final Class<?> clazz, Method method) {
			if (avg < min) {
				return format(avg, min, clazz, method, "at least");
			} else if (avg > max) {
				return format(avg, max, clazz, method, "at most");
			} else {
				throw new RuntimeException();
			}
		}

		private String format(final double avg, final double min, final Class<?> clazz, final Method method, final String bound) {
			return clazz.getName() + ":" + method.getName() + " was expected to process in " + bound + " " + min + "msec but was actually " + avg + "msec";
		}

		protected abstract Queue<Double> loadHistory(final String clazz, final String method);

		private void cleanUp(final Queue<Double> runtimes, final HistoryLength historyConfig) {
			while (runtimes.size() > historyConfig.maximumEntries) {
				runtimes.poll();
			}
		}

		protected abstract void storeHistory(final String clazz, final String method, final Collection<Double> runtimes);
	}

	public static class HistoryLength {

		public static class ClearHistory extends HistoryLength {

			ClearHistory() {
				super(0);
			}
		}

		public static class DefaultHistoryLength extends HistoryLength {

			DefaultHistoryLength() {
				super(5);
			}
		}

		public static final ClearHistory CLEAR_HISTORY = new ClearHistory();

		public static final HistoryLength FIVE_ENTRIES = new DefaultHistoryLength();

		public final int maximumEntries;

		public HistoryLength(final int maximumEntries) {
			this.maximumEntries = maximumEntries;
		}
	}

	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	//
	// L O G G I N G
	//
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	public static abstract class Logger {

		public static enum Level {
			DEBUG, ERROR, INFO
		}

		public static final class LogAllLogger extends Logger {

			public LogAllLogger() {
				logInfo = logDebug = logError = true;
				printerInfo = printerDebug = printerError = System.out;
			}
		}

		public static final class LogNothingLogger extends Logger {

			public LogNothingLogger() {
				logInfo = logDebug = logError = false;
			}
		}

		public static final Logger LOG_ALL = new LogAllLogger();

		public static final Logger LOG_NOTHING = new LogNothingLogger();

		protected boolean logDebug, logError, logInfo;

		protected PrintStream printerDebug, printerError, printerInfo;

		public final void log(final Level level, final String message) {
			if (logInfo && (level == Level.INFO)) {
				printerInfo.print(message);
			} else if (logDebug && (level == Level.DEBUG)) {
				printerDebug.print(message);
			} else if (logError && (level == Level.ERROR)) {
				printerError.print(message);
			}
		}

		public final void logLn(final Level level, final String message) {
			log(level, message + "\n");
		}
	}

	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	//
	// R U N T I M E T E S T C L A S S
	//
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
	// S T A T I C H E L P E R M E T H O D S
	// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

	protected static double avg(final Collection<Double> list) {
		double retval = 0;
		for (final double l : list) {
			retval += l;
		}
		return retval / list.size();
	}

	protected static double avg(final long[] list) {
		double retval = 0;
		for (final long l : list) {
			retval += l;
		}
		return retval / list.length;
	}

	protected static Collection<String> readAllLines(final Path path) {
		assert (path != null);
		final List<String> lines = new ArrayList<String>();
		try (final FileReader reader = new FileReader(path.toFile())) {
			String line = null;
			try (final BufferedReader bufferedReader = new BufferedReader(reader)) {
				while ((line = bufferedReader.readLine()) != null) {
					lines.add(line);
				}
			} catch (final Exception e) {
				e.printStackTrace();
			}
		} catch (final Exception e) {
			e.printStackTrace();
		}
		return lines;
	}

	protected static <K, V> V getOrDefault(final Map<K, V> map, final K key, final V defaultValue) {
		return map.containsKey(key) ? map.get(key) : defaultValue;
	}

	// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
	// F I E L D S
	// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

	protected static boolean disableThisTest = false;

	protected static Logger logger = Logger.LOG_ALL;

	protected static History history = new History.PlainTextFileHistory(logger, ".", "runtime");

	protected static HistoryLength historyLength = HistoryLength.FIVE_ENTRIES;

	private static final String STR_COOLDOWN_PHASE = "Run cooldown phase...";

	private static final String STR_DONE = "[DONE]";

	private static final String STR_EXCEPTION_CONSTRAINT_VIOLATION = "Method under test violates constraints.";

	private static final String STR_EXCEPTION_IN_METHOD = "Exception in method under test.";

	private static final String STR_EXCEPTION_JUNIT = "JUnit test throws assertion.";

	private static final String STR_NO_METHODS = "[NO METHODS DETECTED]";

	private static final String STR_STARTING_CONSTRAINT_TEST = "Starting runtime constraint test: ";

	private static final String STR_SKIP_CONSTRAINT_TEST = "Skip runtime constraint test: ";

	private static final String STR_WARMUP_PHASE = "Run warmup phase...";

	// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
	// P R O T E C T E D M E T H O D S
	// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

	protected void checkConstraintRanges(final Annotations.Constraint constraint) {
		if (((constraint.allowedMinus() != Double.NEGATIVE_INFINITY) && (constraint.allowedMinus() < 0))
			|| ((constraint.allowedPlus() != Double.POSITIVE_INFINITY) && (constraint.allowedPlus() < 0))) {
			throw new RangeException(constraint);
		}
	}

	protected List<Method> extractConstaintedMethods(final Class<? extends Annotation> annotation) throws SecurityException {
		final List<Method> result = new ArrayList<>();
		for (final Method method : this.getClass().getMethods()) {
			if (method.isAnnotationPresent(annotation)) {
				result.add(method);
			}
		}
		return result;
	}

	protected String formatException(final Throwable e, final String headerMessage) {
		assert ((e != null) && (headerMessage != null)) : "Argument is null";

		final StackTraceElement[] st = e.getStackTrace();
		final StringBuilder trace = new StringBuilder(headerMessage);
		trace.append(" (");
		trace.append(e.getClass().getName() + (e.getMessage() != null ? " " + e.getMessage() : "") + ")");
		trace.append("\n\nSTACK TRACE\n\t");
		for (int i = 0; i < st.length; i++) {
			trace.append(st[i].getClassName());
			trace.append(".");
			trace.append(st[i].getMethodName());
			trace.append("\n\t");
		}

		assert ((trace != null) && (trace.length() > 0));
		return trace.toString();
	}

	protected void invokeMethodsWithAnnotation(final Class<? extends Annotation> annotation, final Object instance)
			throws IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		final List<Method> constraintedMethods = extractConstaintedMethods(annotation);
		if (constraintedMethods.isEmpty()) {
			logger.logLn(Level.DEBUG, STR_NO_METHODS);
		} else {
			for (final Method m : constraintedMethods) {
				logger.log(Level.DEBUG, ".");
				m.invoke(instance);
			}
			logger.logLn(Level.DEBUG, STR_DONE);
		}
	}

	protected long measureMethodRuntime(final Method m, final Object instance)
			throws IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		assert ((m != null) && (instance != null)) : "Argument is null";

		final long startTime = System.currentTimeMillis();
		try {
			m.invoke(instance);
		} catch (final Throwable e) {
			if ((e instanceof InvocationTargetException) && (e.getCause() instanceof AssertionError)) {
				((AssertionError) e.getCause()).printStackTrace();
				Assert.fail(formatException((e.getCause()), STR_EXCEPTION_JUNIT));
			} else {
				e.printStackTrace();
				Assert.fail(formatException(e.getCause(), STR_EXCEPTION_IN_METHOD));
			}
		}
		final long delta = System.currentTimeMillis() - startTime;

		assert (delta >= 0);
		return delta;
	}

	protected void runCoolDownPhase(final Object instance) throws IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		logger.log(Level.DEBUG, STR_COOLDOWN_PHASE);
		invokeMethodsWithAnnotation(Annotations.CoolDown.class, instance);
	}

	protected void runTestPhase(final Object instance) throws IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		assert (instance != null) : "Instance is null";

		for (final Method m : extractConstaintedMethods(Annotations.Constraint.class)) {
			final Annotations.Constraint constraint = m.getAnnotation(Annotations.Constraint.class);
			checkConstraintRanges(constraint);
			double avgRuntime = 0;
			History.Result passesTest = History.Result.PASSES;
			for (int i = 0; i < constraint.samples(); i++) {
				avgRuntime = measureMethodRuntime(m, instance);
				passesTest = history.addRun(historyLength, this.getClass(), m, constraint, avgRuntime);
				if (passesTest.testPass) {
					break;
				}
			}
			if (!passesTest.testPass) {
				Assert.fail(formatException(new ViolationException(passesTest.message), STR_EXCEPTION_CONSTRAINT_VIOLATION));
			}
		}
	}

	protected void runWarmUpPhase(final Object instance) throws IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		logger.log(Level.DEBUG, STR_WARMUP_PHASE);
		invokeMethodsWithAnnotation(Annotations.WarmUp.class, instance);
	}

	// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
	// J U N I T E N T R Y P O I N T
	// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

	@Test
	public void entryPoint() {
		if (!disableThisTest) {
			logger.logLn(Level.DEBUG, STR_STARTING_CONSTRAINT_TEST + this.getClass().getName());
			try {
				final Object instance = this.getClass().newInstance();
				runWarmUpPhase(instance);
				runTestPhase(instance);
				runCoolDownPhase(instance);
			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException | InstantiationException e) {
				logger.logLn(Level.ERROR, "Exception during test: " + e.getMessage());
				e.printStackTrace();
				Assert.fail(e.toString());
			}
		} else {
			logger.logLn(Level.DEBUG, STR_SKIP_CONSTRAINT_TEST + this.getClass().getName());
		}
	}
}
