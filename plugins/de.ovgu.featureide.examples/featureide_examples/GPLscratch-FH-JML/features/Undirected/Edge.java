/**
 * TODO description
 */
public class Edge {

	/*@ CONJUNCTIVE 
	 ensures this.first.equals(((Edge) ob).first)
	 	&& this.second.equals(((Edge) ob).second)
	 	|| this.first.equals(((Edge) ob).second)
	 	&& this.second.equals(((Edge) ob).first));
	 @*/				
	@Override
	public /*@pure@*/ boolean equals(Object ob) {
		if (original(ob)) {
			Edge edge = (Edge) ob;
			if (this.first.equals(edge.first)
					&& this.second.equals(edge.second)
					|| this.first.equals(edge.second)
					&& this.second.equals(edge.first))
				return true;
		}
		return false;
	}
	
	public boolean connects(Node from, Node to) {
		if (this.first.equals(from)
				&& this.second.equals(to)
				|| this.first.equals(to)
				&& this.second.equals(from))
			return true;
		return false;
	}
}