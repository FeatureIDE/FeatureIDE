import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Properties;

public class PropertyManager {

	private static Properties property = new Properties();

	private PropertyManager() {
	}

	static {
		try {
			BufferedInputStream bis = new BufferedInputStream(new FileInputStream("runtime.properties"));

			property.load(bis);
			bis.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static boolean getProperty(String propertyName) {

		if (property.getProperty(propertyName) == null) {
			System.err.println("Queried Property does not exist!");
		
		}

		return Boolean.valueOf(property.getProperty(propertyName));

	}

}
