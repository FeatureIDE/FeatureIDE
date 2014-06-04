package com.sleepycat.je;
import com.sleepycat.je.dbi.TruncateResult;
public class Database {
  /** 
 * @deprecated It has not been possible to implement this method with
 * correct transactional semantics without incurring a performance penalty
 * on all Database operations. Truncate functionality has been moved to
 * Environment.truncateDatabase(), which requires that all Database handles
 * on the database are closed before the truncate operation can execute.
 */
  public int truncate(  Transaction txn,  boolean countRecords) throws DatabaseException {
    return new Database_truncate(this,txn,countRecords).execute();
  }
  /** 
 * Internal unchecked truncate that optionally counts records.
 * @deprecated
 */
  int truncateInternal(  Locker locker,  boolean countRecords) throws DatabaseException {
    if (databaseImpl == null) {
      throw new DatabaseException("couldn't find database - truncate");
    }
    this.hook43();
    if (handleLocker.isHandleLockTransferrable()) {
      handleLocker.transferHandleLock(this,locker,false);
    }
    boolean operationOk=false;
    try {
      TruncateResult result=envHandle.getEnvironmentImpl().truncate(locker,databaseImpl);
      databaseImpl=result.getDatabase();
      operationOk=true;
      return countRecords ? result.getRecordCount() : -1;
    }
  finally {
      locker.setHandleLockOwner(operationOk,this,false);
    }
  }
  protected void hook43() throws DatabaseException {
  }
@MethodObject static class Database_truncate {
    Database_truncate(    Database _this,    Transaction txn,    boolean countRecords){
      this._this=_this;
      this.txn=txn;
      this.countRecords=countRecords;
    }
    int execute() throws DatabaseException {
      _this.checkEnv();
      _this.checkRequiredDbState(_this.OPEN,"Can't call Database.truncate");
      _this.checkWritable("truncate");
      this.hook39();
      locker=null;
      this.hook40();
      operationOk=false;
      try {
        locker=LockerFactory.getWritableLocker(_this.envHandle,txn,_this.isTransactional(),true,null);
        _this.acquireTriggerListReadLock();
        this.hook41();
        count=_this.truncateInternal(locker,countRecords);
        for (int i=0; i < _this.triggerList.size(); i+=1) {
          obj=_this.triggerList.get(i);
          if (obj instanceof SecondaryTrigger) {
            secDb=((SecondaryTrigger)obj).getDb();
            secDb.truncateInternal(locker,false);
          }
        }
        operationOk=true;
        return count;
      }
  finally {
        if (locker != null) {
          locker.operationEnd(operationOk);
        }
        this.hook42();
      }
    }
    protected Database _this;
    protected Transaction txn;
    protected boolean countRecords;
    protected Locker locker;
    protected boolean triggerLock;
    protected boolean operationOk;
    protected int count;
    protected Object obj;
    protected SecondaryDatabase secDb;
    protected void hook39() throws DatabaseException {
    }
    protected void hook40() throws DatabaseException {
    }
    protected void hook41() throws DatabaseException {
    }
    protected void hook42() throws DatabaseException {
    }
  }
}
