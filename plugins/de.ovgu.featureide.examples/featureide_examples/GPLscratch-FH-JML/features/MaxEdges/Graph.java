import java.util.List;

/**
 * TODO description
 */
public class Graph {
	private List<Edge> edges;
	private final static Integer MAXEDGES = 10;
	
	/*@ EXPLICIT
	 requires \original && MAXEDGES != null;
	 ensures countEdges() <= MAXEDGES ==> \original;
	 @*/
	public void addEdge(Edge edge) {
		if(countEdges() <= MAXEDGES)
			original(edge);
	}
	
	/*@ PLAIN
	 requires edges != null:
	 ensures \result == edges.size();
	 @*/
	private /*@pure@*/ int countEdges() {
		return edges.size();
	}
}