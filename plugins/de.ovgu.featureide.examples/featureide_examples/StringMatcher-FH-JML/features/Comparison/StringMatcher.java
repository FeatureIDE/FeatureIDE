public  class  StringMatcher {

	/*@public model boolean compare;@*/
	
	/*@
	  @ requires input != null;
	  @ ensures \result <==> compare(input,text);
	  @*/
	public /*@pure@*/ boolean match(String input){
		
		return compare(input,text);
	}

	/*@
	  @ requires a != null && b != null; 
	  @ ensures  \result <==> compare;
	  @*/
	public /*@pure@*/ boolean compare(String a, String b){
		//@ set compare=true;
		return  true;
	}
	
}