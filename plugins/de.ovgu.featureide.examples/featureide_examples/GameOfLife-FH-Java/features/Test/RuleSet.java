


import java.util.Arrays;

class RuleSet {
	public boolean equals(Object o) {
		if(o == null) {
			return false;
		} else if(o instanceof RuleSet) {
			RuleSet rso = (RuleSet) o;
			return Arrays.equals(rso.causesBirth, this.causesBirth) && Arrays.equals(rso.causesDeath, this.causesDeath);
		} else {
			return false;
		}
	}
}