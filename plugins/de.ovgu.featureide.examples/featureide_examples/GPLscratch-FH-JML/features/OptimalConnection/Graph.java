import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.Queue;

import org.w3c.dom.Node;

/**
 * TODO description
 */
public class Graph {

	/*@ PLAIN
	 
	 @*/
	public ArrayList<Node> getConnection(Node source, Node target) {
		setNodesUnvisited();
		return doBFS(new ArrayList<Node>(), source, target);
	}
	
	/*@
	 requires path != null && source != null && target != null;
	 ensures TODO;
	 @*/
	private ArrayList<Node> doBFS(ArrayList<Node> path, Node source, Node target) {
		Queue<Node> q = new LinkedList<Node>();
		q.offer(source);
		source.setVisited(true);
		Node current;
		while(!q.isEmpty()) {
			current = q.poll();
			if (n.equals(target)) {
				path = traverseBackwards(n);
				Collections.reverse(path);
				break;
			}
			
			for(Node n : current.getDestinations() ) {
				if(!n.isVisited) {
					n.setParent(current);
					q.offer(n);
				}
			}
		}
		return path;
	}
	
	private ArrayList<Node> traverseBackwards(ArrayList<Node> path, Node n){
		path.add(n);
		if (n.getParrent() != null)
			traverseBackwards(path, n.getParrent());
		return path;
	}
	
}