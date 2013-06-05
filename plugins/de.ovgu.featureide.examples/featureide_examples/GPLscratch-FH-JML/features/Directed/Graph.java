/**
 * TODO description
 */
public class Graph {

	public void addEdge(Node source, Node dest, double weight) {
		Edge s = new Edge(source, dest, weight);
		if (!source.getNeighbors().contains(s))
			source.getNeighbors().add(s);
	}

}