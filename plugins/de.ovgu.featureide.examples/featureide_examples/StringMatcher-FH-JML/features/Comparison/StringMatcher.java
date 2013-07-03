public  class  StringMatcher {

	/*@public ghost boolean compare;@*/
	
	/*@
	  @ requires input != null;
	  @ ensures \result <==> compare;
	  @*/
	public boolean match(String input){
		
		return compare(input,text);
	}

	/*@
	  @ requires a != null && b != null; 
	  @ ensures  \result <==> compare;
	  @*/
	public boolean compare(String a, String b){
		//@ set compare=true;
		return  true;
	}
	
}