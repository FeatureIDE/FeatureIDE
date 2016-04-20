import java.io.IOException;
import properties.PropertyManager;

public class Main {
	public static void main(String[] args) throws IOException {

		// TODO change the "Composition Mechanism" to "Properties"
		//      in the project's "Properties" > "FeatureIDE" > "Feature Project"

		if (PropertyManager.getProperty("Hello")) {
			System.out.print("Hello");
		}

		if (PropertyManager.getProperty("Beautiful")) {
			System.out.print(" beautiful");
		}

		if (PropertyManager.getProperty("Wonderful")) {
			System.out.print(" wonderful");
		}

		if (PropertyManager.getProperty("World")) {
			System.out.println(" World!");
		}

	}

}
