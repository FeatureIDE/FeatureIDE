package WonderfulWorld;



abstract class Main$$Hello {

	public void print() {
		System.out.print("Hello");
	}
	
	public static void main(String[] args) {
		new Main().print();
	}
	
}



abstract class Main$$Wonderful extends  Main$$Hello  {

	public void print() {
		super.print();
		System.out.print(" wonderful");
	}

}



public class Main extends  Main$$Wonderful  {

	public void print() {
		super.print();
		System.out.print(" world!");
	}

}