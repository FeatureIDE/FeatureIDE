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
	  @ ensures \result ==>(\forall int i; 0 <= i && i < nodes.size() -1;
	  @ 	nodes.toArray()[i].compareTo(nodes.toArray()[i+1]) = -1 );
	  @*/
	public Collection<Node> sortNodes(Collection<Node> nodes) {
		java.util.Set<Node> set = new HashSet<Node>(nodes);
		set = new TreeSet<Node>(set);
		return set;
	}
}