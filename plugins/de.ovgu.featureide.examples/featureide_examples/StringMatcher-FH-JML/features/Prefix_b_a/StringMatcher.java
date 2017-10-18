public class StringMatcher {
	
	/*@
	  @ requires \original;
	  @ ensures \result <==> a.indexOf(b) != -1 && a.startsWith(b);
	  @ assignable \nothing;
	  @*/
	public boolean compare(String a, String b){
		return original(a,b) && a.startsWith(b);
	}
	
}