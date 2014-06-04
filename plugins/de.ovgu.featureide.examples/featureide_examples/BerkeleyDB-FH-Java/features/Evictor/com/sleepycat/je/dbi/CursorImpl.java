package com.sleepycat.je.dbi;
public class CursorImpl {
  private boolean allowEviction=true;
  /** 
 * Disables or enables eviction during cursor operations for an internal
 * cursor. For example, a cursor used to implement eviction should not
 * itself perform eviction. Eviction is enabled by default.
 */
  public void setAllowEviction(  boolean allowed){
    allowEviction=allowed;
  }
  /** 
 * Evict the LN node at the cursor position. This is used for internal
 * databases only.
 */
  public void evict() throws DatabaseException {
    this.hook202();
    setTargetBin();
    targetBin.evictLN(targetIndex);
  }
  protected void hook202() throws DatabaseException {
  }
  protected void hook203() throws DatabaseException {
  }
  /** 
 * Shallow copy. addCursor() is optionally called. Allows inheriting the BIN
 * position from some other cursor.
 */
  public CursorImpl cloneCursor(  boolean addCursor,  CursorImpl usePosition) throws DatabaseException {
    CursorImpl result=original(addCursor,usePosition);
    if (allowEviction) {
      this.hook203();
    }
    return result;
  }
}
