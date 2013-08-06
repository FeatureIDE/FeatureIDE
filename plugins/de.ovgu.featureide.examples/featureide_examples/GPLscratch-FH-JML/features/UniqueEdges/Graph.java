import java.util.Collection;
import java.util.HashSet;
import java.util.TreeSet;


/**
 * TODO description
 */
public class Graph {
	private Collection<Edge> edges;

	public Graph() {
		edges = new HashSet<Edge>();
	}
	
	/*@ \final_method
	 @ requires edges != null && edges instanceof Set<Node>;
	 @ ensures \result == (\forall int i; 0 <= i && i < edges.size() -1;
	 @  	edges.toArray()[i].compareTo(edges.toArray()[i+1]) = -1 );
	 @*/
	public Collection<Edge> sortEdges(Collection<Edge> edges) {
		java.util.Set<Edge> set = new HashSet<Edge>(edges);
		set = new TreeSet<Edge>(set);
		return set;
	}
}