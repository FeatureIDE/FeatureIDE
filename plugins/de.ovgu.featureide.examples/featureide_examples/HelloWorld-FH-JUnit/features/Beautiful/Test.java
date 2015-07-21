/**
 * JUnit test for hello world.
 */
public class Test {
	@org.junit.Test
	public void testBeautiful() throws Exception {
		StringBuilder result = new Main().buildWorld(new StringBuilder());
		assertTrue(result.toString().contains("beautiful"));
	}
}