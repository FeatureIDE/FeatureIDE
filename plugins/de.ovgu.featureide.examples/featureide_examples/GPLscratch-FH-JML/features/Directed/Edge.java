/**
 * TODO description
 */
public class Edge {
	private Node first;
	private Node second;
	
	/*@ \final_method
	 @ requires first != null && second != null; 
	 @ ensures \result ==> first.equals(((Edge) ob).first) &&
	 @  second.equals(((Edge) ob).second); 
	 @*/
	@Override
	public /*@ pure @*/ boolean equals(Object ob) {
		if (original(ob)) {
			Edge edge = (Edge) ob;
			if (first.equals(edge.first)
					&& second.equals(edge.second))
				return true;
		}
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
				+ first.hashCode();
		hash = hashMultiplikator * hash
				+ second.hashCode();
		return hash;
	}

	/*@ \final_method
	 @ requires first != null && second != null; 
	 @ ensures \result ==> (first.equals(from) &&
	 @ 	second.equals(to));
	 @*/
	public /*@pure@*/ boolean connects(Node from, Node to) {
		if (first.equals(from) && second.equals(to))
			return true;
		return false;
	}
	

//	@Override
	public /*@pure@*/ String toString() {
		return original() + first + " --> " + second;
	}

}