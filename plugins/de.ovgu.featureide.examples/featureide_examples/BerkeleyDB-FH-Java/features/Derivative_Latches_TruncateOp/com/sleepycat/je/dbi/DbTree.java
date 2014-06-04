package com.sleepycat.je.dbi;
public class DbTree {
  protected void hook294(  CursorImpl nameCursor) throws DatabaseException {
    nameCursor.releaseBIN();
    original(nameCursor);
  }
  protected void hook295(  CursorImpl nameCursor) throws DatabaseException {
    nameCursor.releaseBIN();
    original(nameCursor);
  }
}
