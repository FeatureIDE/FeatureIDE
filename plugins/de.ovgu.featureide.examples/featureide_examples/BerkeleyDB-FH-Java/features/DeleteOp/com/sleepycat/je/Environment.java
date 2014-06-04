package com.sleepycat.je;
public class Environment {
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public void removeDatabase(  Transaction txn,  String databaseName) throws DatabaseException {
    checkHandleIsValid();
    checkEnv();
    DatabaseUtil.checkForNullParam(databaseName,"databaseName");
    Locker locker=null;
    boolean operationOk=false;
    try {
      locker=LockerFactory.getWritableLocker(this,txn,environmentImpl.isTransactional(),true,null);
      environmentImpl.dbRemove(locker,databaseName);
      operationOk=true;
    }
  finally {
      if (locker != null) {
        locker.operationEnd(operationOk);
      }
    }
  }
  protected boolean hook59(  DatabaseImpl database,  boolean databaseExists) throws DatabaseException {
    if (database != null && !database.isDeleted())     databaseExists=true;
    return original(database,databaseExists);
  }
}
