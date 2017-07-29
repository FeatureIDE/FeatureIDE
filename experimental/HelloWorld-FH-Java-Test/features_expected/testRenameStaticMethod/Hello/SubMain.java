public class SubMain2 extends Main {

	protected void print() {
		System.out.print("Hello SubMain");
	}
	
	public static void mainStatic(String[] args){
		new Main().print();
	}
}