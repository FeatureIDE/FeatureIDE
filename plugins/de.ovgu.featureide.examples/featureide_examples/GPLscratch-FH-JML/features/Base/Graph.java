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

	// print Methods
	public void print() {
		printNodes();
		System.out.println();
		printEdges();

	}

	public void printNodes() {
		System.out.println("### NODES ###");
		for (Node n : nodes) {
			System.out.println(n.getName());
			for(Edge e : n.getNeighbors()) {
				System.out.println("Edge to: " + e.getN2().getName());
			}
		}
	}

	public void printEdges() {
		System.out.println("### EDGES ###");
		for (Edge e : edges) {
			printEdge(e);
		}
	}

	private void printEdge(Edge e) {
		System.out.println(e.getN1().getName() + " - " + e.getN2().getName());
	}

	public void addEdge(Node n1, Node n2) {
		n1.addNeighbor(n2);
		n2.addNeighbor(n1);
	}
	
	// Node Methods
	public void addNode(Node node) {
		if (!hasNode(node)) {
			nodes.add(node);
		}
	}

	public boolean hasNode(Node node) {
		if (getNode(node.getName()) != null)
			return true;
		return false;
	}

	public Node getNode(String nodeName) {
		for (Node n : nodes) {
			if (n.getName().equals(nodeName))
				return n;
		}
		return null;
	}

	public List<Node> getNodes() {
		return nodes;
	}
}