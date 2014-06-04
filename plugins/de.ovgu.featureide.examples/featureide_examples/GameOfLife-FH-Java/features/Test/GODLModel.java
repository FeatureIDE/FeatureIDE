

class GODLModel {	
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(playground);
		return sb.toString();
	}
	
	public boolean equals(Object o) {
		if(o == null) {
			return false;
		} else if(o instanceof GODLModel) {
			GODLModel ogm = (GODLModel) o;
			return playground.equals(ogm.playground) && rules.equals(ogm.rules);
		} else {
			return false;
		}
	}
}