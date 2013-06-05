/**
 * TODO description
 */
public class Node {
	private String name;

	public Node(String name) {
		this.name = name;
	}

	/*@
	 requires name != null; 
	 ensures \result == name; 
	 @*/
	public /*@pure@*/ String getName() {
		return name;
	}

	/*@ REFINEABLE
	 requires ob instanceof Edge && ob != null && 
	 	this.name.equals(((Node) ob).getName());
	 ensures this == ob;
	 also
	 ensures this != ob;
	 @*/
	@Override
	public /*@pure@*/ boolean equals(Object ob) {
		return (ob != null && (ob instanceof Node) && this.name
				.equals(((Node) ob).getName())) ? true : false;
	}
	
	/*@
	 requires name != null; 
	 ensures \result == name; 
	 @*/
	@Override
	public /*@pure@*/ String toString() {
		return name;
	}
}