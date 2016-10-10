public class Edge implements Comparable<Edge>{
	/*@ \conjunctive_contract
	  @ requires ob != null;
	  @ ensures \result ==> ob instanceof Edge;
	  @*/
	@Override
	public /*@pure@*/ boolean equals(Object ob) {
		return (ob instanceof Edge) ? true : false;
	}
	
	private Node first;
	private Node second;

	public Edge(Node first, Node second) {
		this.first = first;
		this.second = second;
	}



	/*@ \conjunctive_contract
	  @ requires first != null && second != null;
	 @*/
	@Override
	public /*@pure@*/ String toString() {
		return "Edge: ";
	}
	
	@Override
	public int compareTo(Edge e) {
		if (this.equals(e))
			return 0;
		int c = this.first.compareTo(e.first);
		if (c == 0)
			c = this.second.compareTo(e.second);
		return c;
	}
}