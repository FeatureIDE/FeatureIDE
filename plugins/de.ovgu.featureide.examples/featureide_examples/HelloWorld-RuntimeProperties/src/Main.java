import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Properties;

public class Main {
	public static void main(String[] args) throws IOException {

		
		if (PropertyManager.getProperty("Hello")) {
			System.out.print("Hello");
		}

		if (PropertyManager.getProperty("beautiful")) {
			System.out.print(" beautiful");
		}

		if (PropertyManager.getProperty("wonderful")) {
			System.out.print(" wonderful");
		}

		if (PropertyManager.getProperty("World")) {
			System.out.print(" World!");
		}

	}


}
