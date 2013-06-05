/**
 * TODO description
 */
public class Edge {
	//@ public invariant weight >= 0;
	private Integer weight = 0;


	/*@ 
	 requires weight != null && ((Edge)ob).weight != null;
	 ensures this.weight == ((Edge)ob).weight;
	 @*/
//	@Override
	public /*@pure@*/ boolean equals(Object ob) {
		if (original(ob) && this.weight == ((Edge)ob).weight) {
			return true;
		}
		return false;
	}
	
	/*@ PLAIN
	 requires weight >= 0;
	 ensures this.weight == weight;
	 @*/
	public void setWeight(Integer weight) {
		this.weight = weight;
	}
}