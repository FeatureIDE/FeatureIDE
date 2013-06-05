import java.util.LinkedList;
import java.util.Queue;

/**
 * TODO description
 */
public class BFS {
	Graph g;
	Queue<Node> q = new LinkedList<Node>();
	Node start;
	Node target;

	public BFS(Graph g, Node n) {
		this.g = g;
		start = g.getNodes().get(0);
		target = n;
	}

	public void run() {
		for (Node n : g.getNodes()) {
			n.setVisited(false);
		}
		q.offer(start);
		start.setVisited(true);
		System.out.println(start + " Node in queue");
		bfs();
	}

	private void bfs() {
		Node currentNode;
		while (!q.isEmpty()) {
			currentNode = q.poll();
			if (currentNode.equals(target)) {
				System.out.println("Zielknoten gefunden: " + currentNode);
				return;
			}
			System.out.println("Expandiere Knote:" + currentNode);
			for (Edge e : currentNode.getNeighbors()) {
				if (!e.getDest().isVisited()) {
					System.out.println(e.getDest() + "Node in queue");
					q.offer(e.getDest());
					e.getDest().setVisited(true);
				}
			}

		}
		System.out.println("Zielknoten nicht gefunden!");
	}
}