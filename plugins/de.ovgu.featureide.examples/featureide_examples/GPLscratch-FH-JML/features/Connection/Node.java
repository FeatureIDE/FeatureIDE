/**
 * TODO description
 */
public class Node {
	private boolean visited;

	/*@ \final_method
	 @ 	ensures \result == visited;
	 @ assignable \nothing;
	 @*/
	public boolean isVisited() {
		return visited;
	}
	
	/*@ \final_method
	 @ 	requires visited != null;
	 @ 	ensures this.visited = visited;
	 @ assignable visited;
	 @*/
	public void setVisited(boolean visited) {
		this.visited = visited;
	}
}