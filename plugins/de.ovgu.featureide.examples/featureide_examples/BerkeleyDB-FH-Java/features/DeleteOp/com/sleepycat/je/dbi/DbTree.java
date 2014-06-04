package com.sleepycat.je.dbi;
public class DbTree {
  /** 
 * Remove the database by deleting the nameLN.
 */
  void dbRemove(  Locker locker,  String databaseName) throws DatabaseException {
    CursorImpl nameCursor=null;
    try {
      NameLockResult result=lockNameLN(locker,databaseName,"remove");
      nameCursor=result.nameCursor;
      if (nameCursor == null) {
        return;
      }
 else {
        nameCursor.delete();
        locker.markDeleteAtTxnEnd(result.dbImpl,true);
      }
    }
  finally {
      if (nameCursor != null) {
        this.hook293(nameCursor);
        nameCursor.close();
      }
    }
  }
  protected void hook293(  CursorImpl nameCursor) throws DatabaseException {
  }
}
