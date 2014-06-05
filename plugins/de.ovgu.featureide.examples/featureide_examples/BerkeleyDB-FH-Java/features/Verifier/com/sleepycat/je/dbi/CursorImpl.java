package com.sleepycat.je.dbi;
public class CursorImpl {
  private static final boolean DEBUG=false;
  private void verifyCursor(  BIN bin) throws DatabaseException {
    if (!bin.getCursorSet().contains(this)) {
      throw new DatabaseException("BIN cursorSet is inconsistent.");
    }
  }
  protected void hook276() throws DatabaseException {
    if (DEBUG) {
      verifyCursor(bin);
    }
    original();
  }
  protected void hook277() throws DatabaseException {
    if (DEBUG) {
      verifyCursor(dupBin);
    }
    original();
  }
  protected void hook278() throws DatabaseException {
    if (DEBUG) {
      if (bin != null) {
        verifyCursor(bin);
      }
      if (dupBin != null) {
        verifyCursor(dupBin);
      }
    }
    original();
  }
@MethodObject static class CursorImpl_getNextDuplicate {
    protected void hook279() throws DatabaseException {
      if (_this.DEBUG) {
        _this.verifyCursor(_this.dupBin);
      }
      original();
    }
  }
}
