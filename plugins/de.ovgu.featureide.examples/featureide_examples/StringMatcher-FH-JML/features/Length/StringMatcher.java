public  class   StringMatcher {
		
	/*@
	  @ requires \original;
	  @ ensures  \result ==> a.length()==b.length();
	  @ ensures \original;
	  @ ensures a.length()!=b.length() ==> !\result;
	  @*/
	public /*@pure@*/ boolean compare(String a, String b){
		
		return  original(a,b) && a.length()==b.length();
	}
}