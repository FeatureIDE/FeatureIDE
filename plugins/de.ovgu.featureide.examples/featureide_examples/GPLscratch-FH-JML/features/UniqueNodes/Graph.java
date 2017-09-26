import java.util.Collection;
import java.util.HashSet;
import java.util.TreeSet;

/**
 * TODO description
 */
public class Graph {
	private Collection<Node> nodes;

	public Graph() {
		nodes = new HashSet<Node>();
	}
	
	/*@ \final_method
	  @ requires nodes != null && nodes instanceof Set<Node>;
	  @ ensures (\forall int i; 0 <= i && i < \result.size()-1;
	  @ 	\result.toArray()[i].compareTo(\result.toArray()[i+1]) < 0 );
	  @ assignable \nothing;
	  @*/
	public Collection<Node> sortNodes(Collection<Node> nodes) {
		java.util.Set<Node> set = new HashSet<Node>(nodes);
		set = new TreeSet<Node>(set);
		return set;
	}
}