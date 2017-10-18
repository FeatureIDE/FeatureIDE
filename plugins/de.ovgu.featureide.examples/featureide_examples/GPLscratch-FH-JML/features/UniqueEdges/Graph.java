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
	 @ requires edges != null && edges instanceof Set<Edge>;
	 @ ensures (\forall int i; 0 <= i && i < \result.size() -1;
	 @  	\result.toArray()[i].compareTo(\result.toArray()[i+1]) < 0 );
	 @ assignable \nothing;
	 @*/
	public Collection<Edge> sortEdges(Collection<Edge> edges) {
		java.util.Set<Edge> set = new HashSet<Edge>(edges);
		set = new TreeSet<Edge>(set);
		return set;
	}
}