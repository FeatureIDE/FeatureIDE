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
package de.ovgu.featureide.core.munge;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.ovgu.featureide.munge.MungeFMComposerExtension;

/**
 * Tests for Munge renaming.
 *
 * @author Jens Meinicke
 */
public class TMungeFMComposerExtension {

	private final MungeFMComposerExtension fmComposerExtension = new MungeFMComposerExtension();

	private static final String OLD_NAME = "Hello";
	private static final String NEW_NAME = "NewFeature";

	private static final String OLD_FILE_CONTENT = "public class Main {\r\n" + "\r\n" + "public static void main(String[] args){\r\n" + "	/*if[Hello]*/\r\n"
		+ "	System.out.print(\"Hello\");\r\n" + "	/*end[Hello]*/\r\n" + "	/*if[Beautiful]*/	\r\n" + "	System.out.print(\" beautiful\");\r\n"
		+ "	/*end[Beautiful]*/\r\n" + "	/*if[Wonderful]*/	\r\n" + "	System.out.print(\" wonderful\");\r\n" + "	/*end[Wonderful]*/\r\n"
		+ "	/*if[World]*/		\r\n" + "	System.out.print(\" world!\");\r\n" + "	/*end[World]*/\r\n" + "	}\r\n" + "}";

	private static final String NEW_FILE_CONTENT = "public class Main {\r\n" + "\r\n" + "public static void main(String[] args){\r\n"
		+ "	/*if[NewFeature]*/\r\n" + "	System.out.print(\"Hello\");\r\n" + "	/*end[NewFeature]*/\r\n" + "	/*if[Beautiful]*/	\r\n"
		+ "	System.out.print(\" beautiful\");\r\n" + "	/*end[Beautiful]*/\r\n" + "	/*if[Wonderful]*/	\r\n" + "	System.out.print(\" wonderful\");\r\n"
		+ "	/*end[Wonderful]*/\r\n" + "	/*if[World]*/		\r\n" + "	System.out.print(\" world!\");\r\n" + "	/*end[World]*/\r\n" + "	}\r\n" + "}";

	@Test
	public void performRenamingsTest_1() {
		assertEquals(fmComposerExtension.performRenamings(OLD_NAME, NEW_NAME, OLD_FILE_CONTENT), NEW_FILE_CONTENT);
	}

}
