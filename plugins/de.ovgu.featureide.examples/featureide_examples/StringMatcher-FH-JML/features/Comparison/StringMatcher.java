import org.junit.Test;

public  class  StringMatcher {

	//@public ghost boolean compare;
	int bla;
	/*@
	  @ requires input != null;
	  @ ensures \result <==> compare;
	  @*/
	public boolean match(String input){
		
		return compare(input,text);
	}


	
	/*@
	  @ requires a != null && b != null; 
	  @ ensures  \result <==> compare;
	  @*/
	public static boolean compare(String a, String b){
		//@ set compare=true;
		return  true;
	}
	
}