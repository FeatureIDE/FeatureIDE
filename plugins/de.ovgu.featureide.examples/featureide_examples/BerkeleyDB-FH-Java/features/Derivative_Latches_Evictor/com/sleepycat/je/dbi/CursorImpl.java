package com.sleepycat.je.dbi;
public class CursorImpl {
  /** 
 * Evict the LN node at the cursor position. This is used for internal
 * databases only.
 */
  public void evict() throws DatabaseException {
    try {
      original();
    }
  finally {
      releaseBINs();
    }
  }
  protected void hook202() throws DatabaseException {
    latchBINs();
    original();
  }
}
