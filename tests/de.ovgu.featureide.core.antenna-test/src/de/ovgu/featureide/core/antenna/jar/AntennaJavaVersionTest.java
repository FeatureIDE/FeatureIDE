package de.ovgu.featureide.core.antenna.jar;

import org.junit.Test;

import antenna.preprocessor.v3.Preprocessor;
import de.ovgu.featureide.fm.core.jar.JavaVersionTest;

/**
 * Checks the Java Version of antenna.jar
 * 
 * @author Jens Meinicke
 */
public class AntennaJavaVersionTest {

	@Test
	public void testJavaVersion() throws Exception {
		JavaVersionTest.testJavaVersion(Preprocessor.class);
	}
}
