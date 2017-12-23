public class SubMain extends Main {

	protected void print() {
		System.out.print("Hello SubMain");
	}
	
	public static void main(String[] args){
		new Main().print();
	}
}