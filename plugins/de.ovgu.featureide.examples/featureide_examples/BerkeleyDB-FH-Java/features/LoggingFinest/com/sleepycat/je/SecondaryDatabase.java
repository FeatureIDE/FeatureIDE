package com.sleepycat.je;
public class SecondaryDatabase {
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the
 * logger alone to conditionalize whether we send this message,
 * we don't even want to construct the message if the level is
 * not enabled.
 */
  void trace(  Level level,  String methodName) throws DatabaseException {
    new SecondaryDatabase_trace(this,level,methodName).execute();
  }
  /** 
 * Adds secondary to primary's list, and populates the secondary if needed.
 */
  private void init(  Locker locker) throws DatabaseException {
    trace(Level.FINEST,"SecondaryDatabase open");
    original(locker);
  }
  protected void hook79(  Transaction txn,  DatabaseEntry key) throws DatabaseException {
    trace(Level.FINEST,"SecondaryDatabase.delete",txn,key,null,null);
    original(txn,key);
  }
  protected void hook80(  Transaction txn,  DatabaseEntry key,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryDatabase.get",txn,key,null,lockMode);
    original(txn,key,lockMode);
  }
  protected void hook81(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryDatabase.getSearchBoth",txn,key,data,lockMode);
    original(txn,key,data,lockMode);
  }
@MethodObject static class SecondaryDatabase_trace {
    SecondaryDatabase_trace(    SecondaryDatabase _this,    Level level,    String methodName){
      this._this=_this;
      this.level=level;
      this.methodName=methodName;
    }
    void execute() throws DatabaseException {
    }
    protected SecondaryDatabase _this;
    protected Level level;
    protected String methodName;
    protected Logger logger;
    protected StringBuffer sb;
  }
}
