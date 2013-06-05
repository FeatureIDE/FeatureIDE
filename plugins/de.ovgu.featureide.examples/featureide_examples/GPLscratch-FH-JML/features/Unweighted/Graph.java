/**
 * TODO description
 */
public class Graph {
	
	// Edge Methods
	public void addEdge(Node n1, Node n2) {
		original(n1,n2);
		if (!hasEdge(n1, n2)) {
			if (!hasNode(n1))
				nodes.add(n1);
			if (!hasNode(n2))
				nodes.add(n2);
			edges.add(new Edge(n1, n2));
		}
	}

	public boolean hasEdge(Node n1, Node n2) {
		if (getEdge(n1, n2) != null)
			return true;
		return false;
	}

	public Edge getEdge(Node n1, Node n2) {
		for (Edge e : edges) {
			if (e.isEdge(n1, n2))
				return e;
		}
		return null;
	}
}