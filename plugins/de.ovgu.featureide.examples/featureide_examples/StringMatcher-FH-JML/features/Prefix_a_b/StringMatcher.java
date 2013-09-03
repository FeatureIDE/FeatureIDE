
public  class   StringMatcher {
	

	/*@
	  @ requires \original;
	  @ ensures \original;
	  @*/
	public  boolean compare(String a, String b){
		boolean result = original(a,b) &&   b.startsWith(a);
		//@ set compare = compare && b.startsWith(a);
		return result;
	}


	
}