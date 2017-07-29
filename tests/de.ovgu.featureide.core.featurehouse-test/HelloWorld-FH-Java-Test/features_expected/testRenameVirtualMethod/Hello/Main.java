public class Main {

	protected void println() {
		System.out.print("Hello");
	}
	
	public static void main(String[] args){
		new Main().println();
	}
	
	public Main(){
	}
	
	protected void print1() {
		System.out.print("print1");
	}
	
}