import java.util.Collection;
import java.util.List;

/**
 * TODO description
 */
public class Graph {
	private Collection<Edge> edges;
	private static Integer MAXEDGES = new Integer(10);
	
	/*@ \final_method
	 @ requires \original && MAXEDGES != null;
	 @ ensures \old(countEdges()) < MAXEDGES ==> \original;
	 @ assignable \nothing;
	 @*/
	public void addEdge(Edge edge) {
		if(countEdges() < MAXEDGES)
			original(edge);
	}
	
	/*@ \final_method
	 @ requires edges != null;
	 @ ensures \result == edges.size();
	 @*/
	private /*@pure@*/ int countEdges() {
		return edges.size();
	}
}