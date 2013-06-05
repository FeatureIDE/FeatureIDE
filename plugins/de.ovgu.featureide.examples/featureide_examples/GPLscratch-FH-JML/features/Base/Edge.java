/**
 * TODO description
 */
public class Edge {
	private Node first, second;

	public Edge(Node first, Node second) {
		this.first = first;
		this.second = second;
	}

	/*@ REFINEABLE
	 requires ob != null;
	 ensures ob instanceof Edge;
	 @*/
//	@Override
	public /*@pure@*/ boolean equals(Object ob) {
		return (ob instanceof Edge) ? true : false;
	}

	/*@ REFINEABLE
	 requires first != null && second != null;
	 @*/
	@Override
	public /*@pure@*/ String toString() {
		return "Edge contains Node: " + first + " and Node " + second;
	}
}