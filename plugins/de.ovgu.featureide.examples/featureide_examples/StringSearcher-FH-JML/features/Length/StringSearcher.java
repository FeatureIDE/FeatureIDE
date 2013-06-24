public  class  StringSearcher {
		
	/*@
	  @ requires \original;
	  @ ensures \original;
	  @ ensures \result <==> \original && a.length()==b.length();
	  @*/
	public /*@pure@*/ boolean compare(String a, String b){
		
		return original(a,b) && a.length()==b.length();
	}
}