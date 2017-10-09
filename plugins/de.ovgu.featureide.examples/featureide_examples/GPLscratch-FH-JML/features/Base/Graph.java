import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
/**
 * Base is the implementation of a simple graph
 */
public class Graph {
	private Collection<Node> nodes;
	private Collection<Edge> edges;
	
	// Base Implementation allowing multiple Edges / Nodes
	public Graph() {
		nodes = new ArrayList<Node>();
		edges = new ArrayList<Edge>();
	}

	/*@
	 @ requires edge != null && nodes.contains(edge.first) && nodes.contains(edge.second);
	 @ ensures hasEdge(edge);
	 @ assignable edges;
	 @*/
	public void addEdge(Edge edge) {
		edges.add(edge);
	}

	/*@ \final_method
	 @ requires node != null;
	 @ ensures nodes.contains(node);
	 @ assignable nodes;
	 @*/
	public void addNode(Node node) {
		nodes.add(node);
	}

	/*@ \final_method
	 @ requires nodes != null;
	 @ assignable \nothing;
	 @*/
	public void print() {
		System.out.println("## NODES ##");
		for (Node n : sortNodes(nodes)) 
			System.out.println("\t"+n);
		
		System.out.println("## EDGES ##");
		for(Edge e : sortEdges(edges))
			System.out.println("\t" + e);
	}
	
	
	/*@ \consecutive_contract
	 @ requires nodes != null && nodes instanceof List<Node>;
	 @ ensures (\forall int i; 0 <= i && i < \result.size()-1;
	 @ 	\result.toArray()[i].compareTo(\result.toArray()[i+1]) <= 0 );
	 @ assignable \nothing;
	 @*/
	public Collection<Node> sortNodes(Collection<Node> nodes) {
		List<Node> list = new ArrayList<Node>(nodes);
		Collections.sort(list);
		return list;
	}
	
	/*@ \consecutive_contract
	 @ requires edges != null && edges instanceof List<Edge>;
	 @ ensures (\forall int i; 0 <= i && i < \result.size()-1;
	 @ 	\result.toArray()[i].compareTo(\result.toArray()[i+1]) <= 0);
	 @ assignable \nothing;
	 @*/
	public Collection<Edge> sortEdges(Collection<Edge> edges) {
		List<Edge> list = new ArrayList<Edge>(edges);
		Collections.sort(list);
		return list;
	}

	/*@ \final_method
	 @ requires edge != null && edges != null;
	 @ ensures \result == (\exists int i; 0 <= i && i < edges.size(); edges.get(i).equals(edge));
	 @*/
	public /*@pure@*/ boolean hasEdge(Edge edge) {
		for(Edge e : edges) {
			if(e.equals(edge))
				return true;
		}
		return false;
	}
	
	/*@ \final_method
	 @ requires from != null && to != null && edges != null;
	 @ ensures \result == (\exists int i; 0 <= i && i < edges.size(); edges.get(i).connects(from, to));
	 @*/
	public /*@pure@*/ boolean hasConnectingEdge(Node from, Node to) {
		for(Edge e : edges) {
			if(e.connects(from, to))
				return true;
		}
		return false;
	}
	
	/*@ \final_method
	 @ 	ensures \result = nodes;
	 @*/
	public /*@pure@*/ Collection<Node> getNodes() {
		return nodes;
	}
	
	/*@ \final_method
 	 @ ensures \result = edges;
 	 @*/
	public /*@pure@*/ Collection<Edge> getEdges() {
		return edges;
	}
}