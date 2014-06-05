package com.sleepycat.je.dbi;
public class DbTree {
  protected void hook296(  Locker locker,  NameLockResult result,  DatabaseImpl newDb) throws DatabaseException, CloneNotSupportedException {
    locker.markDeleteAtTxnEnd(result.dbImpl,true);
    locker.markDeleteAtTxnEnd(newDb,false);
    original(locker,result,newDb);
  }
  protected void hook297(  Locker locker,  DatabaseImpl oldDatabase) throws DatabaseException, CloneNotSupportedException, UnsupportedEncodingException {
    locker.markDeleteAtTxnEnd(oldDatabase,true);
    original(locker,oldDatabase);
  }
}
