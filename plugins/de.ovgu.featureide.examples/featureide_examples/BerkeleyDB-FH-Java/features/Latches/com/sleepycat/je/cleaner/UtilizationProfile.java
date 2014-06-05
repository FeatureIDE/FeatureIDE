package com.sleepycat.je.cleaner;
public class UtilizationProfile {
  protected void hook178(  CursorImpl cursor) throws DatabaseException {
    cursor.releaseBINs();
    original(cursor);
  }
  protected void hook179(  CursorImpl cursor) throws DatabaseException {
    if (cursor != null) {
      cursor.releaseBINs();
      cursor.close();
    }
    original(cursor);
  }
  protected void hook180(  long lsn,  LNLogEntry entry,  DatabaseImpl db,  BIN bin) throws DatabaseException {
    try {
      original(lsn,entry,db,bin);
    }
  finally {
      if (bin != null) {
        bin.releaseLatch();
      }
    }
  }
@MethodObject static class UtilizationProfile_populateCache {
    protected void hook181() throws DatabaseException {
      cursor.releaseBIN();
      original();
    }
    protected void hook182() throws DatabaseException {
      cursor.latchBIN();
      original();
    }
    protected void hook183() throws DatabaseException {
      cursor.releaseBIN();
      original();
    }
    protected void hook184() throws DatabaseException {
      cursor.latchBIN();
      original();
    }
    protected void hook185() throws DatabaseException {
      cursor.releaseBINs();
      original();
    }
  }
}
