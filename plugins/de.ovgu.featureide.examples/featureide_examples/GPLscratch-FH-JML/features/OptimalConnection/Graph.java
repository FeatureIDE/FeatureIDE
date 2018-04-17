import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.Queue;


/**
 * TODO description
 */
public class Graph {

	public ArrayList<Node> getConnection(Node source, Node target) {
		setNodesUnvisited();
		return doBFS(new ArrayList<Node>(), source, target);
	}
	
	/*@ \final_method
	 @ requires path != null && source != null && target != null;
	 @ assignable \nothing;
	 @*/
	// TODO Zeichen Zusätzlich den den Baum/ Bugfix 
	private ArrayList<Node> doBFS(ArrayList<Node> path, Node source, Node target) {
		Queue<Node> q = new LinkedList<Node>();
		q.offer(source);
		source.setVisited(true);
		Node current;
		while(!q.isEmpty()) {
			current = q.poll();
			if (current.equals(target)) {
				path = traverseBackwards(path, current);
				Collections.reverse(path);
				break;
			}
			
			for(Node n : getDestinations(current) ) {
				if(!n.isVisited()) {
					n.setParent(current);
					q.offer(n);
				}
			}
		}
		return path;
	}
	
	/*@ \final_method
	 @ requires path != null && n != null;
	 @ ensures path.contains(n);
	 @ assignable \nothing;
	 @*/
	private ArrayList<Node> traverseBackwards(ArrayList<Node> path, Node n){
		path.add(n);
		if (n.getParent() != null)
			traverseBackwards(path, n.getParent());
		return path;
	}
	
}