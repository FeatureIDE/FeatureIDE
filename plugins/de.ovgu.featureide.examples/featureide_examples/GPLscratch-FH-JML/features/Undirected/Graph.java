import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * TODO description
 */
public class Graph {
	private Collection<Node> nodes;
	private Collection<Edge> edges;
	/*@ \final_method
	 @ requires nodes != null && edges != null && from != null;
	 @ ensures (\forall int i; 0 <= i && i < \result.size(); edges.get(i).connects(from, to));
	 @*/
	public /*@pure@*/ List<Node> getDestinations(Node from) {
		List<Node> destinations = new ArrayList<Node>();
		for (Node n : nodes) {
			for (Edge e : edges) {
				if(e.connects(from, n)) {
					destinations.add(n);
				} else if(e.connects(n,from)) {
					destinations.add(n);
				}
			}
		}
		return destinations;
	}
}