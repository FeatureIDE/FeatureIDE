/**
 * TODO description
 */
public class Edge {
	private Node first;
	private Node second;
	
	/*@ \final_method
	 @ requires first != null && second != null; 
	 @ ensures \result ==> (first.equals(((Edge) ob).first)
	 @ 	&& second.equals(((Edge) ob).second)
	 @ 	|| first.equals(((Edge) ob).second)
	 @ 	&& second.equals(((Edge) ob).first));
	 @*/				
	@Override
	public /*@pure@*/ boolean equals(Object ob) {
		if (original(ob)) {
			Edge edge = (Edge) ob;
			if (first.equals(edge.first)
					&& second.equals(edge.second)
					|| first.equals(edge.second)
					&& second.equals(edge.first))
				return true;
		}
		return false;
	}
	
	/*@ \final_method
	 @ requires first != null && second != null && from != null && to != null; 
	 @ ensures \result ==> first.equals(from)	&& second.equals(to)
	 @ 	|| first.equals(to)	&& second.equals(from);
	 @*/	
	public /*@pure@*/ boolean connects(Node from, Node to) {
		if (first.equals(from) && second.equals(to)
				|| first.equals(to) && second.equals(from))
			return true;
		return false;
	}
	
	/*@ \final_method
	 @ requires first != null && second != null;
	 @ ensures \result > 17;
	 @ assignable \nothing;
	 @*/
	@Override
	public int hashCode() {
		int hash = 17;
		int hashMultiplikator = 79;
		hash = hashMultiplikator * hash
				+ first.hashCode() + second.hashCode();
		return hash;
	}
	

//	@Override
	public /*@pure@*/ String toString() {
		return original()+ first + " -- " + second;
	}

}