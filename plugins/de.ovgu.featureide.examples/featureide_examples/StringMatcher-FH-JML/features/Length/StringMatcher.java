public  class   StringMatcher {
		
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @*/
	public static boolean compare(String a, String b){
		boolean result = original(a,b) && a.length()==b.length();
	//@ set compare = compare && a.length()==b.length();
		return  result;
	}
}