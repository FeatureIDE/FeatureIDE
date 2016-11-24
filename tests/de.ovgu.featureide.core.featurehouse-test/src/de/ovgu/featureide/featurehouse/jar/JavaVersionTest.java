package de.ovgu.featureide.featurehouse.jar;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.net.URISyntaxException;
import java.security.CodeSource;
import java.util.Enumeration;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import org.junit.Test;

import com.sun.xml.internal.ws.org.objectweb.asm.ClassReader;
import com.sun.xml.internal.ws.org.objectweb.asm.ClassWriter;

import composer.FSTGenComposer;

/**
 * Checks the Java Version of FeatureHouse.jar
 * 
 * @author Jens Meinicke
 */
public class JavaVersionTest {

	@Test
	public void testJavaVersion() throws IOException, NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException, URISyntaxException {
		CodeSource source = FSTGenComposer.class.getProtectionDomain().getCodeSource();
		File file = new File(source.getLocation().toURI());
		try (JarFile jarFile = new JarFile(file)) {
			final Enumeration<JarEntry> iterator = jarFile.entries();
			while (iterator.hasMoreElements()) {
				JarEntry entry = iterator.nextElement();
				String name = entry.getName();
				if (!name.endsWith(".class")) {
					continue;
				}
				String className = name.split("\\.")[0];
				ClassReader reader = new ClassReader(className);
				ClassWriter classWriter = new ClassWriter(reader, 0);
				reader.accept(classWriter, 0);
				Field versionField = ClassWriter.class.getDeclaredField("version");
				versionField.setAccessible(true);
				int version = versionField.getInt(classWriter);
				if (version > 51) {
					fail("Class " + className + " version " + version + " ishigher then Java 7");
				}
			}
		}
	}
}
