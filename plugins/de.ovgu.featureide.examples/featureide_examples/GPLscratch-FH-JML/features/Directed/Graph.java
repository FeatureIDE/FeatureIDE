/**
 * TODO description
 */
public class Graph {
	
	public void addEdge(Node n1, Node n2) {
		n1.addNeighbor(n2);
	}
	
	public void printEdge(Edge e) {
		System.out.println(e.getN1().getName() + " -> " + e.getN2().getName());
	}
}