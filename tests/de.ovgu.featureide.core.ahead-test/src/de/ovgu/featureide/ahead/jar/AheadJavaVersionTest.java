package de.ovgu.featureide.ahead.jar;

import org.junit.Test;

import de.ovgu.featureide.fm.core.jar.JavaVersionTest;

/**
 * Checks the Java Version of Ahead jars
 * 
 * @author Jens Meinicke
 */
public class AheadJavaVersionTest {

	@Test
	public void testJavaVersion() throws Exception {
		JavaVersionTest.testJavaVersion(jak2java.ActionDecl.class);
		JavaVersionTest.testJavaVersion(mixin.ActionDecl.class);
		JavaVersionTest.testJavaVersion(jampack.ActionDecl.class);
	}
}
