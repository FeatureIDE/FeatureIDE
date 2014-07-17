

abstract class Main$$Hello2 {

	public void print() {
		System.out.print("Hello");
	}
	
	public static void main(String[] args) {
		new Main().print();
	}
	
}

abstract class Main$$Beautiful2 extends  Main$$Hello2  {

	public void print() {
		super.print();
		System.out.print(" beautiful");
	}

}

public class Main extends  Main$$Beautiful2  {

	public void print() {
		super.print();
		System.out.print(" world!");
	}

}