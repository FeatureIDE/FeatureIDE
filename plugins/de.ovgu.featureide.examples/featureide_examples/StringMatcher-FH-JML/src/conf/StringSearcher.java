public  class StringSearcher {
	 /*@spec_public@*/ private String text;

	/*@ requires mainText != null;
	 assignable this.text;
	 ensures this.text == mainText; @*/
	public StringSearcher(String mainText){
		this.text = mainText;
	}

	/*@ requires input != null;
	 ensures \result <==> compare(input,text); @*/
	public /*@pure@*/ boolean match(String input){
		
		return compare(input,text);
	}

	/*@ requires true;
	 ensures  true; @*/
	 private /*@pure@*/ boolean  compare__wrappee__Comparison  (String a, String b){
		return  true;
	}

	/*@
	 requires a != null && b != null;
	 ensures \result <==>  a.length()==b.length(); @*/
	public /*@pure@*/ boolean compare(String a, String b){
		
		return  a.length()==b.length();
	}


}
