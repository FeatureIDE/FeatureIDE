public  class   StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @ ensures \result <==> b.contains(a);
	  @*/
	public /*@pure@*/ boolean compare(String a, String b){
		
		return original(a,b) && b.contains(a);
	}
	
}