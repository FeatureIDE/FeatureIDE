public class SubMain extends RenamedMain {

	protected void print() {
		System.out.print("Hello SubMain");
	}
	
	public static void main(String[] args){
		new RenamedMain().print();
	}
}