
/**
 * Blind of the hand.
 */
public/* nullable_by_default */class Blind {

  


  /**
   * Increase blinds to next level.
   * @param newSmallBlind Next value of small blind.
   * @param newBigBlind Next value of big blind.
   * @param newAnteSize Next value of next ante.
   */
  /*@ public normal_behavior
      requires 0 <= newSmallBlind & small < newSmallBlind;
      requires 0 <= newBigBlind & big < newBigBlind;
      requires 0 <= newAnteSize & ante < newAnteSize;
      assignable big, small, ante;
      ensures small == newSmallBlind;
      ensures big == newBigBlind;
      ensures ante == newAnteSize;
   */
  public final void increaseBlind(final double newSmallBlind,
      final double newBigBlind, final double newAnteSize) {
    setAnte(newAnteSize);
    setSmall(newSmallBlind);
    setBig(newBigBlind);
    // assert false;
    //assert false;
  }

}