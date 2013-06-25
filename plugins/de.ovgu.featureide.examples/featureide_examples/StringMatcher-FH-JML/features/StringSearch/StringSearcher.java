public  class  StringSearcher {
	

	/*@spec_public@*/ private String text;

		
	/*@
	  @ requires mainText != null;
	  @ assignable this.text;
	  @ ensures this.text == mainText;
	  @*/
	public StringSearcher(String mainText){
		this.text = mainText;
	}
	
	
}