public  class   StringMatcher {
	//@public invariant text != null;
	

	/*@spec_public@*/ private String text;

	/*@
	  @ requires mainText != null;
	  @ assignable this.text;
	  @ ensures this.text == mainText;
	  @*/
	public  StringMatcher(String mainText){
		this.text = mainText;
	}
	
	
}