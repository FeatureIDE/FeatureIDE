package properties;

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Properties;
/**
 * Auto-generated class
 * 
 * PropertyManager helps processing .property files.
 * 
 * @author Matthias Quaas
 * @author Kai Wolf
 *
 */

public class PropertyManager {

	private static Properties property = new Properties();

	private PropertyManager() {
	}

	static {
		try (BufferedInputStream bis = new BufferedInputStream(new FileInputStream("runtime.properties"))) {

			property.load(bis);
			bis.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	/**
	 * Gets value for queried property. Throws error message if it does not exists.
	 * @param propertyName
	 * @return Value of property. 
	 */
	public static boolean getProperty(String propertyName) {

		if (property.getProperty(propertyName) == null) {
			System.err.println("Queried Property '"+propertyName+"' does not exist!");
		}

		return Boolean.valueOf(property.getProperty(propertyName));

	}

}