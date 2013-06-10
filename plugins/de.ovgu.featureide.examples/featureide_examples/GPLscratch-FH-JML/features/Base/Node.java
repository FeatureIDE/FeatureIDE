/**
 * TODO description
 */
public class Node implements Comparable<Node>{
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
	
	/*@
	 requires name != null;
	 ensures \result > 17;
	 @*/
	@Override
	public int hashCode() {
		int hash = 17;
		int hashMultiplikator = 79;
		hash = hashMultiplikator * hash
				+ name.hashCode();
		return hash;
	}
	
	@Override
	public int compareTo(Node n) {
		if (n.getName() == null && this.getName() == null) {
			return 0;
	    }
	    if (this.getName() == null) {
	    	return 1;
	    }
	    if (n.getName() == null) {
	    	return -1;
	    }
	    return this.getName().compareTo(n.getName());
	}
	
}