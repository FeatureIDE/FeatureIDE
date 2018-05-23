/**
 * TODO description
 */
public class Main {

	public static void main(String[] args) {
		if (FM.FeatureModel.valid()) {
			new Main();
		}
	}
	
	private Object a;
	private Object b;
	
	public Main() {
		a = new Application();
		b = new Application();
		getA().account.update(100);
		getB().account.update(200);
		getA().nextDay();
		getB().nextYear();
	}
	
	private Application getA() {
		return (Application)a;
	}
	
	private Application getB() {
		return (Application)b;
	}
}