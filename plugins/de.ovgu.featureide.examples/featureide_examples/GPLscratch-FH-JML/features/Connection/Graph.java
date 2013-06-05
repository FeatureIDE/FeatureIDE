import java.util.ArrayList;

/**
 * TODO description
 */
public class Graph {
	
	// compute transitive closure the get to test if there is an edge
	public boolean hasConnection(Node source, Node target) {
		Graph transitiveClosure = new Graph();
		for(Edge edge : edges) {
			transitiveClosure.addEdge(edge);
		}
		for(Node a : nodes) {
			for(Node b : nodes) {
				for (Node c: nodes) {
					if(transitiveClosure.hasConnectingEdge(a,c)) 
						continue;
					if(transitiveClosure.hasConnectingEdge(a,b) && transitiveClosure.hasConnectingEdge(b,c))
						transitiveClosure.addEdge(new Edge(a,c));
					
				}
			}
		}
		return transitiveClosure.hasConnectingEdge(source, target) ? true : false;
	}
	
	// DO DFS -> Memory efficient but not optimalSolution
	public ArrayList<Node> getConnection(Node source, Node target) {
		
		return null;
//		return doDFS();
	}
	
	public static void main(String args[]) {
		Graph g = new Graph();
		Node a = new Node("a");
		Node b = new Node("b");
		Node c = new Node("c");
		g.addNode(a);
		g.addNode(b);
		g.addNode(c);
		Edge ab = new Edge(a,b);
		Edge bc = new Edge(b,c);
		bc.setWeight(12);
		g.addEdge(ab);
		g.addEdge(bc);
		System.out.println(g.hasConnection(a, c));
	}
}