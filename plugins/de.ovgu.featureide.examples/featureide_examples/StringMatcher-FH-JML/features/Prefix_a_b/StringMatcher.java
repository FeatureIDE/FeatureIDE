public class StringMatcher {

	/*@
	  @ requires \original;
	  @ ensures \result <==> b.indexOf(a) != -1 && b.startsWith(a);
	  @ assignable \nothing;
	  @*/
	public  boolean compare(String a, String b){
		return original(a,b) && b.startsWith(a);
	}

}