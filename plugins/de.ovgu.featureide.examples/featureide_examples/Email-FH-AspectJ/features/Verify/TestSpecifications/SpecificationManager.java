package TestSpecifications;

public class SpecificationManager {
	public static Specification7 spec7;
	public static Specification27 spec27;
	
	public static void setupSpecifications() {
		spec7 = new Specification7();
		spec27 = new Specification27();
		original();
	}	
}
