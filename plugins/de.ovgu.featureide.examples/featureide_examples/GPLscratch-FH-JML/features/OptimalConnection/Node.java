/**
 * TODO description
 */
public class Node {
	private Node parent;
	private boolean visited;

	public boolean isVisited() {
		return visited;
	}

	public void setVisited(boolean visited) {
		this.visited = visited;
	}
	
	public void setParent(Node parent) {
		this.parent = parent;
	}
	
	public Node getParent() {
		return parent;
	}
}