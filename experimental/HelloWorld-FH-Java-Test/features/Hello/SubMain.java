public class SubMain extends Main {

	protected void print() {
		System.out.print("Hello SubMain3");
	}
	
	public static void main(String[] args){
		new Main().print();
	}
	
	protected void print1() {
		System.out.print("print1");
	}

}