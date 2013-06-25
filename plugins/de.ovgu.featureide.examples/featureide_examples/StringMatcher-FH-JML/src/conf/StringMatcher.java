public  class StringMatcher {
	//@public invariant text != null;
 /*@spec_public@*/ private String text;

	/*@ requires mainText != null;
	 assignable this.text;
	 ensures this.text == mainText; @*/
	public  StringMatcher(String mainText){
		this.text = mainText;
	}

	/*@ requires input != null;
	 ensures \result <==> compare(input,text); @*/
	public /*@pure@*/ boolean match(String input){
		
		return compare(input,text);
	}

	/*@ requires true;
	 ensures  true; @*/
	public /*@pure@*/ boolean compare(String a, String b){
		return  true;
	}


}
