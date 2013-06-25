public  class   StringMatcher {
		
	/*@
	  @ ensures \result <==> a.equals(b);
	  @*/
	public /*@pure@*/ boolean compare(String a, String b){
		
		return a.equals(b);
	}
}