import static org.junit.Assert.assertTrue;
/**
 * JUnit test for hello world.
 */
public class Test {
	@org.junit.Test
	public void test() throws Exception {
		Main.main(null);
	}
	
	@org.junit.Test
	public void testHello() throws Exception {
		StringBuilder result = new Main().buildWorld(new StringBuilder());
		assertTrue(result.toString().contains("Hello"));
	}
}