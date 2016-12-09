package de.ovgu.featureide.featurehouse.jar;

import org.junit.Test;

import composer.FSTGenComposer;
import de.ovgu.featureide.fm.core.jar.JavaVersionTest;
import fuji.Main;

/**
 * Checks the Java Version of FeatureHouse jars
 * 
 * @author Jens Meinicke
 */
public class FHJavaVersionTest {

	@Test
	public void testFeatureHouseJavaVersion() throws Exception {
		JavaVersionTest.testJavaVersion(FSTGenComposer.class);
	}
	
	@Test
	public void testFUJIJavaVersion() throws Exception {
		JavaVersionTest.testJavaVersion(Main.class);
	}
}
