/**
 * TODO description
 */
public class Test {
	public static void main(String args[]) {
		Graph g = new Graph();
		Node a = new Node("a");
		Node b = new Node("b");
		Node c = new Node("c");
		Node d = new Node("d");
		g.addNode(a);
		g.addNode(b);
		g.addNode(c);
		g.addNode(d);

		Edge ab = new Edge(a, b);
		Edge ac = new Edge(a, c);
		Edge cd = new Edge(c, d);
		Edge bc = new Edge(b, c);
		g.addEdge(ab);
		g.addEdge(ac);
		g.addEdge(cd);
		g.addEdge(bc);
		System.out.println(g.getConnection(a, b));
	}
}