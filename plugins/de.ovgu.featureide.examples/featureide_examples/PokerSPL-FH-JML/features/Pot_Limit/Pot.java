
/**
 * Pot of the table.
 */
public/* nullable_by_default */class Pot {
  
//TODO: replace assignabel size with original call
  /**
   * Adds the value to pot size.
   *
   * @param addedValue The added value to the pot.
   */
  /*@ public normal_behavior
    	
      requires \original_clause && addedValue <= size;
      assignable size;
   */
  public final void addToPotSize(final double addedValue) {
    original(addedValue);
  }
}
