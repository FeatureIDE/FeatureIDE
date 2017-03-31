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
					int minor = data.readUnsignedShort();
					int major = data.readUnsignedShort();
					if (major > 51) {
						throw new Exception("Class " + name + " is compiled with version higher then Java 7: " + major + "." + minor);
					}
				}
			}
		}
	}
}
