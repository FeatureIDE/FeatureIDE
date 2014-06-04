package com.sleepycat.je.dbi;
public class DbTree {
  /** 
 * Return true if the operation succeeded, false otherwise.
 */
  boolean dbRename(  Locker locker,  String databaseName,  String newName) throws DatabaseException {
    CursorImpl nameCursor=null;
    try {
      NameLockResult result=lockNameLN(locker,databaseName,"rename");
      nameCursor=result.nameCursor;
      if (nameCursor == null) {
        return false;
      }
 else {
        nameCursor.delete();
        nameCursor.putLN(newName.getBytes("UTF-8"),new NameLN(result.dbImpl.getId()),false);
        result.dbImpl.setDebugDatabaseName(newName);
        return true;
      }
    }
 catch (    UnsupportedEncodingException UEE) {
      throw new DatabaseException(UEE);
    }
 finally {
      if (nameCursor != null) {
        this.hook298(nameCursor);
        nameCursor.close();
      }
    }
  }
  protected void hook298(  CursorImpl nameCursor) throws DatabaseException {
  }
}
