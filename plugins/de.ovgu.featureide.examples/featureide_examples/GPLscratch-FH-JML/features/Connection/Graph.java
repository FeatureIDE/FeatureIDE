import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * TODO description
 */
public class Graph {
	private Collection<Node> nodes;
	private Collection<Edge> edges;
	
	// compute transitive closure to test if there is an edge
	/*@ \final_method
	 @ requires nodes != null && edges != null && source != null && target != null;
	 @*/
	public /*@pure@*/ boolean hasConnection(Node source, Node target) {
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
	
	/*@ \final_method
	 @ requires connection != null && source != null && target != null;
	 @ ensures \result ==> (\forall int i; 0 <= i && i < connection.size() -1; 
	 @ 	hasConnection(connection.get(i), connection.get(i+1)));
	 @*/
	public /*@pure@*/ boolean isConnection(ArrayList<Node> connection,Node source, Node target ){
		for(int i = 0; i < connection.size()-1; i++) {
			if (!hasConnection(connection.get(i), connection.get(i+1)))
				return false;
		}
		return true;
	}
	
	// BFS oder DFS abhängig deren auswahl -> Shortest PATH als Verfeinerung
	// DO DFS -> Memory efficient but not optimalSolution
	/*@ \final_contract
	 @ 	requires source != null && target != null;
	 @ 	ensures hasConnection(source, target) ==> isConnection(\result, source, target);
	 @  assignable nodes;
	 @*/
	public ArrayList<Node> getConnection(Node source, Node target) {
		setNodesUnvisited();
		return doDFS(new ArrayList<Node>(), source, target);
	}
	
	/*@ \final_method
	 @ requires path != null && source != null && target != null;
	 @ assignable \nothing;
	 @*/
	private ArrayList<Node> doDFS(ArrayList<Node> path, Node source, Node target) {
		source.setVisited(true);
		path.add(source);
		if (source.equals(target))
			return path;
			
		for (Node n : getDestinations(source)) {
			if (!n.isVisited() && doDFS(path, n, target) != null)
				return path;
		}
		
		path.remove(source);
		return null;
	}
	
	/*@  \final_method
	 @ requires nodes != null;
	 @ ensures (\forall int i; 0 <= i && i < nodes.size(); 
	 @ 	nodes.get(i).visible = false);
	 @ assignable nodes;
	 @*/
	private void setNodesUnvisited() {
		for (Node n : nodes) {
			n.setVisited(false);
		}
	}
}