

/**
 * Dealer of the table.
 */
public /* nullable_by_default */class Dealer {


  /** The pot. */
  /*@ spec_public @*/private Pot pot;

  public Dealer(){
	  initDealer();
  }
  /**
   * Instantiates a new dealer.
   */
  private void initDealer() {
   
  original();
   this.pot = new Pot(0);
  }
  

}
