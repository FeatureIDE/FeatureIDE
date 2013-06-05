import java.util.LinkedList;
import java.util.List;

/**
 * TODO description
 */
public class Node {
	private String name;
	private List<Edge> neighbors;
	
	public Node(String name){
		this.name = name;
		this.neighbors = new LinkedList<Edge>();
	}
	
	public void addNeighbor(Node n) {
		if (!hasNeighbor(n))
			neighbors.add(new Edge(this, n));
	}

	public boolean hasNeighbor(Node n) {
		if (getNeighborEdge(n) != null)
			return true;
		return false;
	}

	public Edge getNeighborEdge(Node n) {
		for (Edge e : neighbors) {
			if (e.getN2().getName().equals(n.getName()))
				return e;
		}
		return null;
	}
	
	public String getName() {
		return name;
	}
	
	public List<Edge> getNeighbors(){
		return neighbors;
	}
}