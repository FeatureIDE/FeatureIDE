public class Main {

	public static void main(String[] args){
		//#ifdef Hello
		System.out.print("Hello");
		//#endif
		//#ifdef Beautiful
		System.out.print(" beautiful");
		//#endif
		//#ifdef Wonderful
//@		System.out.print(" wonderful");	
		//#endif
		//#ifdef World	
		System.out.print(" world!");
		//#endif
		
		System.out.println();
		
		HelloWorld.doSomething();
	}
}
