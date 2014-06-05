package com.sleepycat.je.dbi;
public class CursorImpl {
@MethodObject static class CursorImpl_getNextDuplicate {
    protected void hook200() throws DatabaseException {
      _this.latchBIN();
      try {
        original();
      }
  finally {
        _this.releaseBIN();
      }
    }
    protected void hook201() throws DatabaseException {
      duplicateRoot.latch();
      try {
        original();
      }
  finally {
        duplicateRoot.releaseLatch();
      }
    }
  }
}
