import static org.junit.Assert.*;

import org.junit.Test;

public class MainTest {

	//#if Hello
	@org.junit.Test
	public void testHello() throws Exception {
		StringBuilder result = new Main().buildWorld(new StringBuilder());
		assertTrue(result.toString().contains("Hello"));
	}
	//#endif
	
	//#if Beautiful
//@	@org.junit.Test
//@	public void testBeautiful() throws Exception {
//@		StringBuilder result = new Main().buildWorld(new StringBuilder());
//@		assertTrue(result.toString().contains("beautiful"));
//@	}
	//#endif
	
	//#if Wonderful
	@org.junit.Test
	public void testWonderful() throws Exception {
		StringBuilder result = new Main().buildWorld(new StringBuilder());
		assertTrue(result.toString().contains("wonderful"));
	}
	//#endif
	
	//#if World
	@org.junit.Test
	public void testWorld() throws Exception {
		StringBuilder result = new Main().buildWorld(new StringBuilder());
		assertTrue(result.toString().contains("world"));
	}
	//#endif
}
