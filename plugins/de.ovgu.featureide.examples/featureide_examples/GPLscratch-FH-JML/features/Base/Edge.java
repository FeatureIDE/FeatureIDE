/**
 * TODO description
 */
public class Edge {
	private Node n1, n2;
	public boolean isEdge(Node n1, Node n2) {
		if((this.n1.getName().equals(n1.getName())
				|| this.n1.getName().equals(n2.getName()))
				&& (this.n2.getName().equals(n1.getName())
				|| this.n2.getName().equals(n2.getName())))
			return true;
		return false;
	}
	
	public Node getN1() {
		return n1;
	}
	
	public Node getN2() {
		return n2;
	}
}