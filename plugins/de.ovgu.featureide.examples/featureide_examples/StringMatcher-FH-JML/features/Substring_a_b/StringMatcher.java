public class StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \result <==> b.indexOf(a) != -1;
	  @ assignable \nothing;
	  @*/
	public boolean compare(String a, String b){
		return original(a,b) && b.indexOf(a) != -1;
	}
	
}