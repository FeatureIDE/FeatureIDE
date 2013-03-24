package TestSpecifications;

public class SpecificationManager {
	public static Specification3 spec3;
	public static Specification4 spec4;
	
	public static void setupSpecifications() {
		spec3 = new Specification3();
		spec4 = new Specification4();
		original();
	}	
}
