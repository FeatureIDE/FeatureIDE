package com.sleepycat.je;
public class Environment {
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public long truncateDatabase(  Transaction txn,  String databaseName,  boolean returnCount) throws DatabaseException {
    checkHandleIsValid();
    checkEnv();
    DatabaseUtil.checkForNullParam(databaseName,"databaseName");
    Locker locker=null;
    boolean operationOk=false;
    long count=0;
    try {
      locker=LockerFactory.getWritableLocker(this,txn,environmentImpl.isTransactional(),true,null);
      count=environmentImpl.truncate(locker,databaseName,returnCount);
      operationOk=true;
    }
  finally {
      if (locker != null) {
        locker.operationEnd(operationOk);
      }
    }
    return count;
  }
}
