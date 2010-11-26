package HelloWorld;

public class Hello{

	public Hello(){
		print();
	}
	
	protected void print() {
		System.out.print("Hello");
	}
	
	public static void main(String[] args){
		new Hello();
	}
}