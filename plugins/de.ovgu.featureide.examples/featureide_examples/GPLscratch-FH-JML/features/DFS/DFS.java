import java.util.LinkedList;
import java.util.Queue;
import java.util.Stack;

/**
 * TODO description
 */
public class DFS {
	Graph g;
	Node start;
	Node target;
	String pre = "";

	public DFS(Graph g, Node n) {
		this.g = g;
		start = g.getNodes().get(0);
		target = n;
	}

	public void run() {
		for (Node n : g.getNodes()) {
			n.setVisited(false);
		}
		System.out.println("Startknoten in Stack " + start);
		System.out.println("Knoten gefunden: " + dfs(start));
	}

	private Node dfs(Node n) {
		System.out.println(pre + "Expand: " + n);
		pre += "\t";
		n.setVisited(true);
		if (n.equals(target)) {
			return n;
		}
		for (Edge e : n.getNeighbors()) {
			if (!e.getDest().isVisited()) {
				System.out.println(pre + "Nächster Knoten: " + e.getDest());
				Node r = dfs(e.getDest());
				if (r != null)
					return r;
			}
		}
		pre = pre.substring(0, pre.length() - 1);

		return null;

	}
}