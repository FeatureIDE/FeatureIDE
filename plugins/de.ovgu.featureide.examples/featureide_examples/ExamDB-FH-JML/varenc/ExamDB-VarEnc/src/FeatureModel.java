public class FeatureModel {
	
	public static final int ExamDB = 0;
	public static final int BonusPoints = 1;
	public static final int BackOut = 2;
	public static final int Statistics = 3;

	private static boolean[] configuration = new boolean[4];
	
    /*@ public invariant
      @   fm();
      @*/  
	
	static {
		// virtual initialization of the configuration
		// valid fm is assumed afterwards
	}
	
	public /*@pure@*/ static boolean fm() {
		return !(f(BonusPoints) || f(BackOut) || f(Statistics)) || f(ExamDB);
	}
	
	public /*@pure@*/ static boolean f(int feature) {
		return configuration[feature];
	}

}
