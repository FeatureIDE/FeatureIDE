/**
 * TODO description
 */
public class Node {
	private Node parent;
	
	/*@ \final_method
	 @ requires parrent != null;
 	 @ ensures \result == visited;
 	 @ assignable parent;
 	 @*/
	public void setParent(Node parent) {
		this.parent = parent;
	}
	
	/*@ \final_method
 	 @ ensures \result == parrent;
 	 @ assignable \nothing;
 	 @*/
	public Node getParent() {
		return parent;
	}
}