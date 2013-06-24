public  class  StringSearcher {
	
	
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @ ensures \result <==> a.startsWith(b);
	  @*/
	public /*@pure@*/ boolean compare(String a, String b){
		return original(a,b) &&   a.startsWith(b);
	}
	

	
}