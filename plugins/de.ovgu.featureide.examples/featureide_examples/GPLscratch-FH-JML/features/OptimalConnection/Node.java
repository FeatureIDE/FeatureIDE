/**
 * TODO description
 */
public class Node {
	private Node parent;
	
	/*@ \final_method
	 @ requires parrent != null;
 	 @ ensures \result == visited;
 	 @*/
	public void setParent(Node parent) {
		this.parent = parent;
	}
	
	/*@ \final_method
 	 @ ensures \result == parrent;
 	 @*/
	public Node getParent() {
		return parent;
	}
}