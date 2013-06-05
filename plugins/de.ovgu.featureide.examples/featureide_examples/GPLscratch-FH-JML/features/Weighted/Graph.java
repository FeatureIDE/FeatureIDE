/**
 * TODO description
 */
public class Graph {
	public void printEdge(Edge e) {
		original(e);
		System.out.println("\b Weight: " + e.getWeight());
	}
	// Edge Methods
	public void addEdge(Node n1, Node n2, int weight) {
		original(n1, n2, weight);
		if (!hasEdge(n1, n2, weight)) {
			if (!hasNode(n1))
				nodes.add(n1);
			if (!hasNode(n2))
				nodes.add(n2);
			edges.add(new Edge(n1, n2, weight));
		}
	}

	public boolean hasEdge(Node n1, Node n2, int weight) {
		if (getEdge(n1, n2, weight) != null)
			return true;
		return false;
	}

	public Edge getEdge(Node n1, Node n2, int weight) {
		for (Edge e : edges) {
			if (e.isEdge(n1, n2) && e.getWeight() == weight)
				return e;
		}
		return null;
	}
}