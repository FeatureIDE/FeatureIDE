/**
 * JUnit test for hello world.
 */
public class Test {
	@org.junit.Test
	public void testWorld() throws Exception {
		StringBuilder result = new Main().buildWorld(new StringBuilder());
		assertTrue(result.toString().contains("World"));
	}
}