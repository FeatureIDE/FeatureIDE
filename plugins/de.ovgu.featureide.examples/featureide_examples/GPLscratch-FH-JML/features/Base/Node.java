/**
 * TODO description
 */
public class Node implements Comparable<Node>{
	private String name;

	/*@ \final_method
	 @ 	requires name != null;
	 @ 	ensures this.name = name;
	 @  assignable name;
	 @*/
	public Node(String name) {
		this.name = name;
	}

	/*@ \final_method
	 @ 	ensures \result == name; 
	 @*/
	public /*@pure@*/ String getName() {
		return name;
	}

	/*@ \final_method
	 @ requires ob != null; 
	 @ ensures \result ==> ob instanceof Edge
	 @ 	&& name.equals(((Node) ob).getName());
	 @*/
	@Override
	public /*@pure@*/ boolean equals(Object ob) {
		return (ob != null && (ob instanceof Node) && name
				.equals(((Node) ob).getName())) ? true : false;
	}

	
	/*@ \final_method
	 @ requires name != null; 
	 @ ensures \result == name; 
	 @*/
	@Override
	public /*@pure@*/ String toString() {
		return name;
	}
	 
	/*@ \final_method
	 @ requires name != null;
	 @ ensures \result > 17;
	 @ assignable \nothing;
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