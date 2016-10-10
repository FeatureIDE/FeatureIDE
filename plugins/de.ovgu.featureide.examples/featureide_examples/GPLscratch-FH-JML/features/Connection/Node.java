/**
 * TODO description
 */
public class Node {
	private boolean visited;

	/*@ \final_method
	 @ 	ensures \result == visited;
	 @*/
	public boolean isVisited() {
		return visited;
	}
	
	/*@ \final_method
	 @ 	requires visited != null;
	 @ 	ensures this.visited = visited;
	 @*/
	public void setVisited(boolean visited) {
		this.visited = visited;
	}
}