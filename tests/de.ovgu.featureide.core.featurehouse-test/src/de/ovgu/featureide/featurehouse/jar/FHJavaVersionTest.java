package de.ovgu.featureide.featurehouse.jar;

import org.junit.Test;

import composer.FSTGenComposer;
import de.ovgu.featureide.fm.core.jar.JavaVersionTest;

/**
 * Checks the Java Version of FeatureHouse.jar
 * 
 * @author Jens Meinicke
 */
public class FHJavaVersionTest {

	@Test
	public void testJavaVersion() throws Exception {
		JavaVersionTest.testJavaVersion(FSTGenComposer.class);
	}
}
