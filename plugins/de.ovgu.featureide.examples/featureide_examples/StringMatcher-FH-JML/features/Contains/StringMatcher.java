public  class   StringMatcher {
	

	/*@
	  @ requires a != null && b != null;
	  @ ensures \result <==> a.indexOf(b) != -1;
	  @*/
	public static /*@pure@*/ boolean contains(String a, String b){
	//	return a.indexOf(b) != -1;
	return a.contains(b);
	}
	
}