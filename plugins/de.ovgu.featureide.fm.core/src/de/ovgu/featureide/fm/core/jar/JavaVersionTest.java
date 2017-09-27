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
package de.ovgu.featureide.fm.core.jar;

import java.io.DataInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.security.CodeSource;
import java.util.Enumeration;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * Checks the Java Version of the classes in he same jar file.
 *
 * @author Jens Meinicke
 */
public class JavaVersionTest {

	/**
	 * Checks the Java Version of all class files in the same jar as the given class.
	 *
	 * @throws Exception if the version of a class is higher then Java 7, or the jar cannot be read.
	 */
	public static void testJavaVersion(final Class<?> c) throws Exception {
		final CodeSource source = c.getProtectionDomain().getCodeSource();
		final File file = new File(source.getLocation().toURI());
		try (JarFile jarFile = new JarFile(file)) {
			final Enumeration<JarEntry> iterator = jarFile.entries();
			while (iterator.hasMoreElements()) {
				final JarEntry entry = iterator.nextElement();
				final String name = entry.getName();
				if (!name.endsWith(".class")) {
					continue;
				}
				try (InputStream in = jarFile.getInputStream(entry); DataInputStream data = new DataInputStream(in)) {
					if (0xCAFEBABE != data.readInt()) {
						throw new IOException("invalid header");
					}
					final int minor = data.readUnsignedShort();
					final int major = data.readUnsignedShort();
					if (major > 51) {
						throw new Exception("Class " + name + " is compiled with version higher then Java 7: " + major + "." + minor);
					}
				}
			}
		}
	}
}
