/**
 * TODO description
 */
public class Graph {
	private final static int MAXEDGES = 10;
	private int amountEdges = 0;
	
	/*@ EXPLICIT
	 requires \original && amountEdges <= MAXEDGES;
	 ensures \original && amoundEdges == \old(amountEdges) +1;
	 @*/
	public void addEdge(Edge edge) {
		amountEdges++;
		original(edge);
	}
}