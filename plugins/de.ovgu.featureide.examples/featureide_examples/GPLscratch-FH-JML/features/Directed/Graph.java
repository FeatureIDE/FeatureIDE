/**
 * TODO description
 */
public class Graph {

	/*@
	 * requires !source.getNeighbors().contains(new Edge(source, dest, weight))
	 * ensures source.getNeighbors().add(new Edge(source, dest, weight));
	 */
	public void addEdge(Node source, Node dest, double weight) {
		Edge s = new Edge(source, dest, weight);
		if (!source.getNeighbors().contains(s))
			source.getNeighbors().add(s);
	}

}