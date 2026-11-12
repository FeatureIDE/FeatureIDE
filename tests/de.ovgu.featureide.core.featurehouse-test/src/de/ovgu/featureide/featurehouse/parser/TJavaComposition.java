/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import cide.gparser.ParseException;
import composer.CmdLineInterpreter;
import composer.CompositionException;
import composer.FSTGenComposer;
import composer.ICompositionErrorListener;
import composer.IParseErrorListener;

/**
 * Composes two features whose Java code uses syntax added after Java 1.5 with FeatureHouse, the same way FeatureIDE does in FeatureHouseComposer.
 *
 * @author Philipp Hehnle
 */
public class TJavaComposition {

	private static final String BASE_LAMBDA = "private java.util.function.Function<Integer, Integer> square = x -> x * x;";
	private static final String BASE_PATTERN = "String describe(Object o) {\n"
		+ "\t\treturn switch (o) {\n"
		+ "\t\t\tcase null -> \"null\";\n"
		+ "\t\t\tcase String s when s.isEmpty() -> \"empty\";\n"
		+ "\t\t\tcase Integer i -> \"\"\"\n"
		+ "\t\t\t\tnumber\n"
		+ "\t\t\t\t\"\"\";\n"
		+ "\t\t\tdefault -> o.toString();\n"
		+ "\t\t};\n"
		+ "\t}";
	private static final String BASE_RUN = "void run(java.util.List<String> names) {\n"
		+ "\t\tnames.forEach(System.out::println);\n"
		+ "\t}";
	private static final String EXT_RUN = "void run(java.util.List<String> names) {\n"
		+ "\t\toriginal(names);\n"
		+ "\t\ttry (java.io.StringReader r = new java.io.StringReader(\"x\")) {\n"
		+ "\t\t\tnames.removeIf(n -> n.length() > 0b1010);\n"
		+ "\t\t} catch (IllegalStateException | IllegalArgumentException e) {\n"
		+ "\t\t}\n"
		+ "\t}";
	private static final String EXT_FIELD = "private Runnable printer = () -> System.out.println(1_000);";

	@Rule
	public TemporaryFolder folder = new TemporaryFolder();

	@Test
	public void composesFeaturesWithNewJavaSyntax() throws IOException {
		final File features = folder.newFolder("features");
		writeClass(new File(features, "Base"), BASE_LAMBDA, BASE_PATTERN, BASE_RUN);
		writeClass(new File(features, "Ext"), EXT_RUN, EXT_FIELD);

		final File configuration = folder.newFile("product.config");
		Files.write(configuration.toPath(), "Base\nExt\n".getBytes(StandardCharsets.UTF_8));
		final File output = folder.newFolder("src");

		final List<String> errors = new ArrayList<>();
		final FSTGenComposer composer = new FSTGenComposer(false);
		composer.addParseErrorListener(new IParseErrorListener() {

			@Override
			public void parseErrorOccured(ParseException e) {
				errors.add(e.getMessage());
			}
		});
		composer.addCompositionErrorListener(new ICompositionErrorListener() {

			@Override
			public void parseErrorOccured(CompositionException e) {
				errors.add(e.getMessage());
			}
		});
		composer.run(new String[] { CmdLineInterpreter.INPUT_OPTION_EQUATIONFILE, configuration.getAbsolutePath(), CmdLineInterpreter.INPUT_OPTION_BASE_DIRECTORY,
			features.getAbsolutePath(), CmdLineInterpreter.INPUT_OPTION_OUTPUT_DIRECTORY, output.getAbsolutePath() + "/",
			CmdLineInterpreter.INPUT_OPTION_NO_CONFIG_OUTPUT_DIR });
		assertEquals("FeatureHouse reported errors", new ArrayList<String>(), errors);

		final File composed = new File(output, "Main.java");
		assertTrue("composed file is missing", composed.isFile());
		final String result = new String(Files.readAllBytes(composed.toPath()), StandardCharsets.UTF_8);

		// members only defined in one feature are copied unchanged
		assertContains(result, BASE_LAMBDA);
		assertContains(result, BASE_PATTERN);
		assertContains(result, EXT_FIELD);
		// the refined method calls the renamed original method of feature Base (FeatureHouse makes it private)
		assertContains(result, BASE_RUN.replace("void run(", "private void  run__wrappee__Base  ("));
		assertContains(result, EXT_RUN.replace("original(names);", "run__wrappee__Base(names);"));
	}

	private static void writeClass(File featureFolder, String... members) throws IOException {
		assertTrue(featureFolder.mkdirs());
		final StringBuilder source = new StringBuilder("public class Main {\n");
		for (final String member : members) {
			source.append("\n\t").append(member).append("\n");
		}
		source.append("}\n");
		Files.write(new File(featureFolder, "Main.java").toPath(), source.toString().getBytes(StandardCharsets.UTF_8));
	}

	private static void assertContains(String text, String expected) {
		assertTrue("expected:\n" + expected + "\n\nin composed file:\n" + text, text.contains(expected));
	}
}
