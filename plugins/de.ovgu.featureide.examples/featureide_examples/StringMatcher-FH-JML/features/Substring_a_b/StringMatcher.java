public  class   StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \result ==> contains(a,b);
	  @*/
	public /*@pure@*/ boolean compare(String a, String b){
		
		return original(a,b) && contains(a,b);
		
	}
	
	

	
}