

/**
 * Dealer of the table.
 */
public /*nullable_by_default*/ class Dealer {


  /** The blind. */
  /*@spec_public@*/ private Blind blind = new Blind(0, 0, 0);


  private void initDealer() {
	original();
    this.blind = new Blind(0, 0, 0);
  
  }
  



}
