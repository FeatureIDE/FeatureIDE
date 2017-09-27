/**
 * TODO description
 */
public class Edge {
	//@ public invariant weight >= 0;
	private Integer weight = 0;


	/*@ \conjunctive_contract
	 @ requires weight != null;
	 @ ensures \result ==> weight == ((Edge)ob).weight;
	 @*/
	public /*@pure@*/ boolean equals(Object ob) {
		if (original(ob) && weight == ((Edge)ob).weight) {
			return true;
		}
		return false;
	}
	
	/*@ \final_method
	 @ requires weight != null && weight >= 0;
	 @ ensures this.weight = weight;
	 @ assignable weight;
	 @*/
	public void setWeight(Integer weight) {
		this.weight = weight;
	}
	
	/*@ \final_contract
	 @ requires weight != null;
	 @*/
//	@Override
	public /*@pure@*/ String toString() {
		return original() + "Weight " + weight  + ": ";
	}
}