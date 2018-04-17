package br.ufal.ic.colligens.controllers.core;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.List;
import java.util.regex.Pattern;

import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.util.ProjectConfigurationErrorLogger;

/**
 * provisional class until we change to the CDT internal builder
 *
 * @author Francisco Dalton
 * @author Thiago Emmanuel
 *
 */
public class CPPWrapper {

	private final String GCC_PATH = Colligens.getDefault().getPreferenceStore().getString("GCC");
	private final MessageConsole console;

	public CPPWrapper() {
		// ConsolePlugin plugin = ConsolePlugin.getDefault();
		// IConsoleManager conMan = plugin.getConsoleManager();
		// console = new MessageConsole("TypeChefConsole", null);
		// conMan.addConsoles(new IConsole[] { console });

		console = findConsole("TypeChefConsole");

	}

	private MessageConsole findConsole(String name) {
		final ConsolePlugin plugin = ConsolePlugin.getDefault();
		final IConsoleManager conMan = plugin.getConsoleManager();
		final IConsole[] existing = conMan.getConsoles();
		for (int i = 0; i < existing.length; i++) {
			if (name.equals(existing[i].getName())) {
				return (MessageConsole) existing[i];
			}
		}
		// no console found, so create a new one
		final MessageConsole myConsole = new MessageConsole(name, null);
		conMan.addConsoles(new IConsole[] { myConsole });
		return myConsole;
	}

	public void runCompiler(List<String> packageArgs) {
		packageArgs.add(0, GCC_PATH);
		final ProcessBuilder processBuilder = new ProcessBuilder(packageArgs);

		BufferedReader input = null;
		BufferedReader error = null;
		final MessageConsoleStream consoleOut = console.newMessageStream();

		try {
			final Process process = processBuilder.start();
			input = new BufferedReader(new InputStreamReader(process.getInputStream(), Charset.availableCharsets().get("UTF-8")));
			error = new BufferedReader(new InputStreamReader(process.getErrorStream(), Charset.availableCharsets().get("UTF-8")));
			boolean x = true;
			while (x) {
				try {
					String line;
					if ((line = error.readLine()) != null) {
						final ProjectConfigurationErrorLogger prjConfi = ProjectConfigurationErrorLogger.getInstance();
						// the string that comes here, have
						// /variant00x/variant00x/
						// that will be used by the compiler to generate the
						// executable
						final String s = packageArgs.get(packageArgs.size() - 1);
						// let's "clean" it...
						final int lastFileSeparator = s.lastIndexOf(System.getProperty("file.separator"));
						final String variantPath = s.substring(0, lastFileSeparator);
						prjConfi.addConfigurationWithError(variantPath);
						consoleOut.println("Variant Name: " + s.substring(lastFileSeparator));

						do {
							// use pattern to avoid errors in Windows OS
							final String pattern = Pattern.quote(System.getProperty("file.separator"));
							final String[] errorLine = line.split(pattern);
							consoleOut.println(errorLine[errorLine.length - 1]);
							Colligens.getDefault().logWarning(line);
						} while ((line = error.readLine()) != null);
						consoleOut.println();
					}

					try {
						process.waitFor();
					} catch (final InterruptedException e) {
						consoleOut.println(e.toString());
						Colligens.getDefault().logError(e);
					}
					final int exitValue = process.exitValue();
					if (exitValue != 0) {
						throw new IOException("The process doesn't finish normally (exit=" + exitValue + ")!");
					}
					x = false;
				} catch (final IllegalThreadStateException e) {
					consoleOut.println(e.toString());
					Colligens.getDefault().logError(e);
				}
			}
		} catch (final IOException e) {
			// consoleOut.println("The Project contains errors! " +
			// e.getMessage());
			Colligens.getDefault().logError(e);
		} finally {
			try {
				if (input != null) {
					input.close();
				}
			} catch (final IOException e) {
				Colligens.getDefault().logError(e);
			} finally {
				if (error != null) {
					try {
						error.close();
					} catch (final IOException e) {
						Colligens.getDefault().logError(e);
					}
				}
			}
		}
	}

	public void runPreProcessor(List<String> packageArgs, String preProcessorOutput) {
		packageArgs.add(0, "-C"); // do not discard comments
		packageArgs.add(0, "-P"); // do not generate linemarkers
		packageArgs.add(0, "-w"); // Suppress all warning
		packageArgs.add(0, "-no-integrated-cpp");
		packageArgs.add(0, "-nostdinc");
		packageArgs.add(0, "-E");
		packageArgs.add(0, GCC_PATH);
		final ProcessBuilder processBuilder = new ProcessBuilder(packageArgs);

		BufferedReader input = null;
		BufferedReader error = null;
		String errorLog = "";

		try {
			final Process process = processBuilder.start();
			input = new BufferedReader(new InputStreamReader(process.getInputStream(), Charset.availableCharsets().get("UTF-8")));
			error = new BufferedReader(new InputStreamReader(process.getErrorStream(), Charset.availableCharsets().get("UTF-8")));
			boolean x = true;

			final File outputFile = new File(preProcessorOutput);
			while (x) {
				try {
					String line;
					try {

						final FileWriter fileW = new FileWriter(outputFile);
						final BufferedWriter buffW = new BufferedWriter(fileW);

						while ((line = input.readLine()) != null) {
							buffW.write(line + "\n");
						}

						while ((line = error.readLine()) != null) {
							errorLog += line + "\n";
						}
						buffW.close();
						fileW.close();
					} catch (final Exception e) {
						e.printStackTrace();
						Colligens.getDefault().logError(e);
					}

					try {
						process.waitFor();
					} catch (final InterruptedException e) {
						System.out.println(e.toString());
						Colligens.getDefault().logError(e);
					}
					final int exitValue = process.exitValue();
					if (exitValue != 0) {
						if (!errorLog.contains("error: no include path in which to search for")) {
							outputFile.deleteOnExit();
							throw new IOException("The process doesn't finish normally (exit=" + exitValue + ")!");
						}
					}

					x = false;
				} catch (final IllegalThreadStateException e) {
					Colligens.getDefault().logError(e);
				}
			}

		} catch (final IOException e) {
			System.out.println(e.toString());
			Colligens.getDefault().logError(e);
		} finally {
			try {
				if (input != null) {
					input.close();
				}

			} catch (final IOException e) {
				Colligens.getDefault().logError(e);
			} finally {
				if (error != null) {
					try {
						error.close();
					} catch (final IOException e) {
						Colligens.getDefault().logError(e);
					}
				}
			}
		}

	}
}
