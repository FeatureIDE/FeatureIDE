import java.util.List;
import java.util.ArrayList;

/**
 * Base is the implementation of a simple graph
 */
public class Graph {
	private List<Node> nodes;
	private List<Edge> edges;

	public Graph() {
		nodes = new ArrayList<Node>();
		edges = new ArrayList<Edge>();
	}

	/*@ EXPLICIT
	 requires edge!= null && nodes.contains(edge.first) && nodes.contains(edge.second);
	 ensures hasEdge(edge);
	 @*/
	public void addEdge(Edge edge) {
		if (!edges.contains(edge))
			edges.add(edge);
	}

	/*@
	 requires node != null;
	 ensures nodes.contains(node);
	 @*/
	public void addNode(Node node) {
		if (!nodes.contains(node))
			nodes.add(node);
	}

	public void print() {
		// TODO Implement
	}

	// public void search(Node n) {
	// System.out.println("Startknoten: " + nodes.get(0) + " Gesucht: " + n);
	// }

	/*@ PLAIN
	 requires  edge != null;
	 ensures \result =(\exist int i; 0 <= i && i < edges.size); edges.get(i).equals(edge));
	 @*/
	public /*@pure@*/ boolean hasEdge(Edge edge) {
		for(Edge e : edges) {
			if(e.equals(edge))
				return true;
		}
		return false;
	}
	
	public /*@pure@*/ boolean hasConnectingEdge(Node from, Node to) {
		for(Edge e : edges) {
			if(e.connects(from, to))
				return true;
		}
		return false;
	}
}