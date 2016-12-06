package de.ovgu.featureide.featurehouse.jar;

import org.junit.Ignore;
import org.junit.Test;

import composer.FSTGenComposer;
import fuji.Main;
import de.ovgu.featureide.fm.core.jar.JavaVersionTest;

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
	
	@Test@Ignore
	public void testFUJIJavaVersion() throws Exception {
		JavaVersionTest.testJavaVersion(Main.class);
	}
}
