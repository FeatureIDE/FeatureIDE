/**
 * TODO description
 */
public class Graph {
	public void search(Node n) {
		original(n);
		DFS dfs = new DFS(this, n);
		dfs.run();
		
	}
}