import java.util.List;
import java.util.ArrayList;

/**
 * Base is the implementation of a simple graph
 */
public class Graph {
	private List<Node> nodes;

	public Graph() {
		nodes = new ArrayList<Node>();
	}

	public void print() {
		for (Node n : nodes) {
			System.out.println("# NODE " + n.getName()
					+ " mit folgenden Kanten: ");
			for (Edge e : n.getNeighbors()) {
				System.out.println(e);
			}
		}
	}
	
	public void search(Node n) {
		System.out.println("Startknoten: " + nodes.get(0) + " Gesucht: " + n);
	}

	// add Methods
	public void addEdge(Node source, Node dest) {
		addEdge(source, dest, Double.POSITIVE_INFINITY);
	}

	// TODO WEIGHT JA / NEIN?
	/*@
	 * requires !source.getNeighbors().contains(new Edge(source, dest, weight))
	 * ensures source.getNeighbors().add(new Edge(source, dest, weight));
	 * ensures addEdge(dest, source, weight)
	 */
	public void addEdge(Node source, Node dest, double weight) {
		Edge s = new Edge(source, dest, weight);
		if (!source.getNeighbors().contains(s)) {
			source.getNeighbors().add(s);
			//add Edge from src -> dest
			addEdge(dest, source, weight);
		}
	}

	
	/*@
	 * requires !nodes.contains(node)
	 * ensures nodes.add(node)
	 */
	public void addNode(Node node) {
		if (!nodes.contains(node))
			nodes.add(node);
	}

	public List<Node> getNodes() {
		return nodes;
	}
}