/**
 * TODO description
 */
public class Edge {
	/*@ CONJUNCTIVE
	 * requires ob != null 
	 * ensures this.first.equals(((Edge) ob).first) &&
	 	this.second.equals(((Edge) ob).second)); 
	 * 
	 * @
	 */
	@Override
	public/* @pure@ */boolean equals(Object ob) {
		if (original(ob)) {
			Edge edge = (Edge) ob;
			if (this.first.equals(edge.first)
					&& this.second.equals(edge.second))
				return true;
		}
		return false;
	}

	public boolean connects(Node from, Node to) {
		if (this.first.equals(from) && this.second.equals(to))
			return true;
		return false;
	}
}