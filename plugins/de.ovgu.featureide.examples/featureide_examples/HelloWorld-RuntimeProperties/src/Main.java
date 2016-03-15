import java.io.IOException;

public class Main {
	public static void main(String[] args) throws IOException {

		
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
