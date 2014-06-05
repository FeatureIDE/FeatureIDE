package com.sleepycat.je.tree;
public class BIN {
  /** 
 * For each cursor in this BIN's cursor set, ensure that the cursor is
 * actually referring to this BIN.
 */
  public void verifyCursors(){
    if (cursorSet != null) {
      Iterator iter=cursorSet.iterator();
      while (iter.hasNext()) {
        CursorImpl cursor=(CursorImpl)iter.next();
        if (getCursorBINToBeRemoved(cursor) != this) {
          BIN cBin=getCursorBIN(cursor);
          assert cBin == this;
        }
      }
    }
  }
}
