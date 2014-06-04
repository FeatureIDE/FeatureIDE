package com.sleepycat.je.dbi;
public class CursorImpl {
  protected void hook203() throws DatabaseException {
    database.getDbEnvironment().getEvictor().doCriticalEviction();
    original();
  }
  /** 
 * Reset a cursor to an uninitialized state, but unlike close(), allow it to
 * be used further.
 */
  public void reset() throws DatabaseException {
    original();
    if (allowEviction) {
      database.getDbEnvironment().getEvictor().doCriticalEviction();
    }
  }
  /** 
 * Close a cursor.
 * @throws DatabaseExceptionif the cursor was previously closed.
 */
  public void close() throws DatabaseException {
    original();
    if (allowEviction) {
      database.getDbEnvironment().getEvictor().doCriticalEviction();
    }
  }
}
