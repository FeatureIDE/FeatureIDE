package TestSpecifications;

public class SpecificationManager {	
	public static Specification1_8 spec1_8;
	public static Specification9 spec9;
	public static Specification6 spec6;
	
	public static void setupSpecifications() {
		spec1_8 = new Specification1_8();
		spec9 = new Specification9();
		spec6 = new Specification6();
		original();
	}	
}
