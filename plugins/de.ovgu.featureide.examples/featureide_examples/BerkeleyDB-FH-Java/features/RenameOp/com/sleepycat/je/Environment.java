package com.sleepycat.je;
public class Environment {
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public void renameDatabase(  Transaction txn,  String databaseName,  String newName) throws DatabaseException {
    DatabaseUtil.checkForNullParam(databaseName,"databaseName");
    DatabaseUtil.checkForNullParam(newName,"newName");
    checkHandleIsValid();
    checkEnv();
    Locker locker=null;
    boolean operationOk=false;
    try {
      locker=LockerFactory.getWritableLocker(this,txn,environmentImpl.isTransactional(),true,null);
      environmentImpl.dbRename(locker,databaseName,newName);
      operationOk=true;
    }
  finally {
      if (locker != null) {
        locker.operationEnd(operationOk);
      }
    }
  }
}
