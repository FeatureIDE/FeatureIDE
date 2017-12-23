public class SubMain extends Main {

	protected void println() {
		System.out.print("Hello SubMain");
	}
	
	public static void main(String[] args){
		new Main().println();
	}
}