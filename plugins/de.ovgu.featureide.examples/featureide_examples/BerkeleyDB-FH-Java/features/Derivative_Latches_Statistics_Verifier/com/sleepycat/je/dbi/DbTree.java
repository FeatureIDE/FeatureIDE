package com.sleepycat.je.dbi;
public class DbTree {
  protected void hook291(  CursorImpl cursor) throws DatabaseException {
    cursor.releaseBINs();
    original(cursor);
  }
}
