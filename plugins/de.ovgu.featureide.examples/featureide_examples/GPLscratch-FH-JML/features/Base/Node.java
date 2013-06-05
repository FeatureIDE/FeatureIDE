import java.util.ArrayList;
import java.util.List;

/**
 * TODO description
 */
public class Node {
	private String name;
	// adjazenzlist
	private List<Edge> neighbors;

	public Node(String name) {
		this.name = name;
		this.neighbors = new ArrayList<Edge>();
	}

	public String getName() {
		return name;
	}

	public List<Edge> getNeighbors() {
		return neighbors;
	}

	@Override
	public boolean equals(Object ob) {
		return (ob != null && (ob instanceof Node) && this.name
				.equals(((Node) ob).getName())) ? true : false;
	}
	
	@Override
	public String toString() {
		return name;
	}
}