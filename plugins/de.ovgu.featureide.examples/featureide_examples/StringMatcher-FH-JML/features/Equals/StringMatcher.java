public class StringMatcher {
		
	/*@
	  @ requires \original;
	  @ ensures \result <==> a.equals(b);
	  @*/
	public  boolean compare(String a, String b){
		return original(a,b) && a.equals(b);
	}
	
}