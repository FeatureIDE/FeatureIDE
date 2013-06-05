/**
 * TODO description
 */
public class Test {
	public static void main(String args[]) {
		testEdge();
	}
	
	static void testEdge() {
		Edge e1 = new Edge(new Node("a"), new Node("b"));
		Edge e2 = new Edge(new Node("b"), new Node("a"));
		Edge e3 = new Edge(new Node("b"), new Node("c"));
		
		System.out.println(e1.equals(e2));
		System.out.println(e2.equals(e3));
		System.out.println(e3.equals(e1));
		System.out.println(e3.equals(e3));
	}
}