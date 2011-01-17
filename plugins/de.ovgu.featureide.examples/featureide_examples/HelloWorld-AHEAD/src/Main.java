

abstract class Main$$Hello {

	public void print() {
		System.out.print("Hello");
	}
	
	public static void main(String[] args) {
		new Main().print();
	}
	
}

public class Main extends  Main$$Hello  {

	public void print() {
		super.print();
		System.out.print(" world!");
	}

}