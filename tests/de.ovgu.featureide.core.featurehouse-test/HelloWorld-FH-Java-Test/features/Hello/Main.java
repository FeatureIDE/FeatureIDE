public class Main {

	protected void print() {
		System.out.print("Hello");
	}
	
	public static void main(String[] args){
		new Main().print();
	}
	
	public Main(){
	}
	
	protected void print1() {
		System.out.print("print1");
	}
	
}