package com.sleepycat.je.dbi;
public class DbTree {
  protected void hook306(  boolean allowEviction,  CursorImpl idCursor) throws DatabaseException, UnsupportedEncodingException {
    idCursor.setAllowEviction(allowEviction);
    original(allowEviction,idCursor);
  }
  protected void hook307(  boolean allowEviction,  CursorImpl nameCursor) throws DatabaseException, UnsupportedEncodingException {
    nameCursor.setAllowEviction(allowEviction);
    original(allowEviction,nameCursor);
  }
  protected void hook308(  boolean allowEviction,  CursorImpl nameCursor) throws DatabaseException, UnsupportedEncodingException {
    nameCursor.setAllowEviction(allowEviction);
    original(allowEviction,nameCursor);
  }
  protected void hook309(  boolean allowEviction,  CursorImpl idCursor) throws DatabaseException {
    idCursor.setAllowEviction(allowEviction);
    original(allowEviction,idCursor);
  }
  protected void hook310(  boolean allowEviction,  CursorImpl idCursor) throws DatabaseException {
    idCursor.setAllowEviction(allowEviction);
    original(allowEviction,idCursor);
  }
}
