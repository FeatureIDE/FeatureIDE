/*
 * 
 */


/**
 * A poker player.
 */
public /*nullable_by_default*/ class Player {


  /** The bank. */
  private /*@spec_public@*/ double bank;


  /*@ 
      public invariant 0 <= bank;
   */

  /**
   * Instantiates a new player.
   * @param newId
   *          player's Id
   * @param initAmount
   *          the init amount
   */
  /*@ assignable bank;
      ensures bank == initAmount;
   */
  private void initPlayer(final int newId, final double initAmount){
	  
	  original(newId,initAmount);
	  }

  /**
   * @return the bank amount
   */
  /*@ public normal_behavior
      ensures \result >= 0;
      ensures \result == bank ;
   */
  public /*@pure@*/ double getBank() {
    //@ assert false;
    //@ assert false;
    return this.bank;
  }


  /**
   * Adds amount addValue to the player's bank.
   * @param value
   *          the value
   */
  /*@ public normal_behavior
      requires addValue >= 0;
      requires getBank() + addValue >= 0;
      assignable bank;
      ensures bank == \old(getBank()) + addValue;
   */
  public final void addToBank(final double addValue) {
    setBank(getBank() + addValue);

  }

  /**
   * Call.
   * @param betValue The value that calling costs.
   */
  /*@ public normal_behavior
      requires 0 < callValue ;
      requires 0 <= getBank() - callValue;
      assignable bank;
      ensures bank == \old(getBank()) - callValue;
   */
  public final void call(final double callValue) {
    setBank(getBank() - callValue);
    //@ assert false;
    //@ assert false;
  }


  /**
   * Raise.
   * @param betValue
   *          The value of the raise bet.
   */
  /*@ public normal_behavior
      requires 0 < betValue ;
      requires 0 <= getBank() - betValue;
      assignable bank;
      ensures bank == \old(getBank()) - betValue;
   */
  public final void raise(final double betValue) {
    setBank(getBank() - betValue);
    //@ assert false;
    //@ assert false;
  }





  /*@ public normal_behavior
  requires value >= 0;
  requires getBank() - addValue >= 0;
  assignable bank;
  ensures bank == \old(getBank()) - addValue;
*/
  public final void subtractFromBank(final double value) {
    setBank(getBank() - value);

  }

  /**
   * @param newBank the new bank amount.
   */
  /*@ requires newBank >= 0;
      assignable bank;
      ensures bank == newBank;
   */
  public final void setBank(final double newBank) {
    this.bank = newBank;
  
  }

  

}
