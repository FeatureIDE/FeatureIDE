/**
 * TODO description
 */
public class Edge {

//	@Override
	/*
	 * @ requires original_spec(?) && this.weight == ((Edge)ob).getWeight()
	 */
	public boolean equals(Object ob) {
		if (original(ob) && this.weight == ((Edge)ob).getWeight()) {
			return true;
		}
		return false;
	}
}