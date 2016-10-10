
/**
 * The button that defines where the deal starts from.
 */
public /*nullable_by_default*/ class Button {

  /** The position. */
  private /*@spec_public@*/ int position;

  /**
   * Instantiates a new button.
   */
  /*@ public normal_behavior
      assignable position;
      ensures position == 0;
   */
  public Button() {
    this.position = 0;
  }

  /**
   * @return the position
   */
  /*@ public normal_behavior
      requires position >= 0;
      ensures \result >= 0;
      ensures position == \result;
   */
  public final /*@pure@*/ int getPosition() {
    // assert false;
    return position;
  }

  /**
   * @param newPosition the new position
   */
  /*@ public normal_behavior
      requires newPosition >=0;
      assignable position;
      ensures position == newPosition;
   */
  public final void setPosition(final int newPosition) {
    this.position = newPosition;
    //@ assert false;
    //@ assert false;
  }
  /**
   * Next dealer.
   */
  public final /*@pure@*/ void nextDealer() {
    //TODO table calculations to find next valid position.
    //@ assert false;
    //@ assert false;
  }
}
