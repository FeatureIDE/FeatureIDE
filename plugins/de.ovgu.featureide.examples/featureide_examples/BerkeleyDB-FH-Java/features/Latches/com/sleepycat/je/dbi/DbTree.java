package com.sleepycat.je.dbi;
public class DbTree {
  protected void hook299(  CursorImpl cursor) throws DatabaseException {
    cursor.releaseBINs();
    original(cursor);
  }
  protected void hook300(  NameLockResult result) throws DatabaseException, UnsupportedEncodingException {
    result.nameCursor.releaseBIN();
    original(result);
  }
  protected void hook301(  NameLockResult result) throws DatabaseException {
    result.nameCursor.releaseBIN();
    original(result);
  }
  protected void hook302(  NameLockResult result) throws DatabaseException {
    result.nameCursor.releaseBIN();
    original(result);
  }
  protected void hook303(  CursorImpl nameCursor) throws DatabaseException, UnsupportedEncodingException {
    nameCursor.releaseBIN();
    original(nameCursor);
  }
  protected void hook304(  CursorImpl idCursor) throws DatabaseException {
    idCursor.releaseBIN();
    original(idCursor);
  }
  protected void hook305(  CursorImpl cursor) throws DatabaseException {
    cursor.releaseBINs();
    original(cursor);
  }
}
