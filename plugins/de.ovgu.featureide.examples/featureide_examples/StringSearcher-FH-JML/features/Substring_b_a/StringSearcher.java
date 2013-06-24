public  class  StringSearcher {
	
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @ ensures \result <==> a.contains(b);
	  @*/
	public /*@pure@*/ boolean compare(String a, String b){
		return original(a,b) &&   a.contains(b);
	}
	
}