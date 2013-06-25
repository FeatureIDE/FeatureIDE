public  class  StringSearcher {

	
	/*@
	  @ requires input != null;
	  @ ensures \result <==> compare(input,text);
	  @*/
	public /*@pure@*/ boolean match(String input){
		
		return compare(input,text);
	}

	/*@
	  @ requires true;
	  @ ensures  true;
	  @*/
	public /*@pure@*/ boolean compare(String a, String b){
		return  true;
	}
	
}