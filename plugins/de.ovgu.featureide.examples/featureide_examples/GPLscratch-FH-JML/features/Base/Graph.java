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

	/*@ EXPLICIT
	 requires node != null;
	 ensures nodes.contains(node);
	 @*/
	public void addNode(Node node) {
		if (!nodes.contains(node))
			nodes.add(node);
	}

	/*@ EXPLICIT TODO
	 requires nodes != null;
	 @*/
	public void print() {
		System.out.println("## NODES ##");
		for (Node n : nodes) 
			System.out.println("\t"+n);
		
		System.out.println("## EDGES ##");
		for(Edge e : edges)
			System.out.println("\t" + e);
	}

	/*@ PLAIN
	 requires edge != null && edges != null;
	 ensures \result == (\exists int i; 0 <= i && i < edges.size); edges.get(i).equals(edge));
	 @*/
	public /*@pure@*/ boolean hasEdge(Edge edge) {
		for(Edge e : edges) {
			if(e.equals(edge))
				return true;
		}
		return false;
	}
	
	/*@ PLAIN
	 requires from != null && to != null && edges != null
	 ensures result == (\exist int i; 0 <= i && < edges.size; edges.get(i).connects(from, to));
	 @*/
	public /*@pure@*/ boolean hasConnectingEdge(Node from, Node to) {
		for(Edge e : edges) {
			if(e.connects(from, to))
				return true;
		}
		return false;
	}
	
	/*@PLAIN
	 	ensures \result = nodes;
	 @*/
	public /*@pure@*/ List<Node> getNodes() {
		return nodes;
	}
	
	/*@PLAIN
 		ensures \result = edges;
 	@*/
	public /*@pure@*/ List<Edge> getEdges() {
		return edges;
	}
}