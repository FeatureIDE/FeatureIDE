import core_0.Main;

/**
 * This class is added, as DeltaJ does not support static methods. Hence, it
 * is not possible to create a main method and to execute DeltaJ programs 
 * without this wrapper.
 * 
 * @author Thomas Thuem
 */
public class HelloWorld_DeltaJ {
	
	public static void main(String[] args) {
		new Main().print();
	}
	
}