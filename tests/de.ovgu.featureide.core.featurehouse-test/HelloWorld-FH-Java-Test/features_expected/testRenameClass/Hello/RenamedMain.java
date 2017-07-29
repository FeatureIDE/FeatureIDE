public class RenamedMain {

	protected void print() {
		System.out.print("Hello");
	}
	
	public static void main(String[] args){
		new RenamedMain().print();
	}
	
	public RenamedMain(){
	}
	
	protected void print1() {
		System.out.print("print1");
	}
	
}