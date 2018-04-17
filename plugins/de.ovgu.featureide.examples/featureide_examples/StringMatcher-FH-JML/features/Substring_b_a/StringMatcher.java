public class StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \result <==> a.indexOf(b) != -1;
	  @ assignable \nothing;
	  @*/
	public boolean compare(String a, String b){
		return original(a,b) && a.indexOf(b) != -1;
	}
	
}