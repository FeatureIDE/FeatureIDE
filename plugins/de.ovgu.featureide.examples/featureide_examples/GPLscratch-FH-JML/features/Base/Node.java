/**
 * TODO description
 */
public class Node {
	private String name;

	public Node(String name) {
		this.name = name;
	}

	/*@ PLAIN
	 requires name != null; 
	 ensures \result == name; 
	 @*/
	public /*@pure@*/ String getName() {
		return name;
	}

	/*@ EXPLICIT
	 requires ob != null; 
	 ensures \result ==> ob instanceof Edge
	 	&& name.equals(((Node) ob).getName());
	 @*/
	@Override
	public /*@pure@*/ boolean equals(Object ob) {
		return (ob != null && (ob instanceof Node) && name
				.equals(((Node) ob).getName())) ? true : false;
	}
	
	/*@ EXPLICIT
	 requires name != null; 
	 ensures \result == name; 
	 @*/
	@Override
	public /*@pure@*/ String toString() {
		return name;
	}
}