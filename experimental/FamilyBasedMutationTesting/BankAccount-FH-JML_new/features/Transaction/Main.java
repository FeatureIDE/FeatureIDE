/**
 * TODO description
 */
public class Main {


	public Main() {
		new Transaction().transfer(getA().account, getB().account, 30);
		new Transaction().transfer(getB().account, getA().account, 100);
	}
	
}