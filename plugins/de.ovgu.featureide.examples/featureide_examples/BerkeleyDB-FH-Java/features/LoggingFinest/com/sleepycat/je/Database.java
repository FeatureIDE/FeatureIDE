package com.sleepycat.je;
public class Database {
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  void trace(  Level level,  String methodName,  Transaction txn,  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    new Database_trace(this,level,methodName,txn,key,data,lockMode).execute();
  }
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  void trace(  Level level,  String methodName,  Transaction txn,  CursorConfig config) throws DatabaseException {
    new Database_trace2(this,level,methodName,txn,config).execute();
  }
  protected void hook44() throws DatabaseException {
    trace(Level.FINEST,"Database.close: ",null,null);
    original();
  }
  protected void hook45(  Transaction txn,  DatabaseEntry key) throws DatabaseException {
    trace(Level.FINEST,"Database.openSequence",txn,key,null,null);
    original(txn,key);
  }
  protected void hook46(  Transaction txn,  CursorConfig cursorConfig) throws DatabaseException {
    trace(Level.FINEST,"Database.openCursor",txn,cursorConfig);
    original(txn,cursorConfig);
  }
  protected void hook47(  Transaction txn,  DatabaseEntry key) throws DatabaseException {
    trace(Level.FINEST,"Database.delete",txn,key,null,null);
    original(txn,key);
  }
  protected void hook48(  Transaction txn,  DatabaseEntry key,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Database.get",txn,key,null,lockMode);
    original(txn,key,lockMode);
  }
  protected void hook49(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Database.getSearchBoth",txn,key,data,lockMode);
    original(txn,key,data,lockMode);
  }
  protected void hook50(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    trace(Level.FINEST,"Database.put",txn,key,data,null);
    original(txn,key,data);
  }
  protected void hook51(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    trace(Level.FINEST,"Database.putNoOverwrite",txn,key,data,null);
    original(txn,key,data);
  }
  protected void hook52(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    trace(Level.FINEST,"Database.putNoDupData",txn,key,data,null);
    original(txn,key,data);
  }
@MethodObject static class Database_trace2 {
    Database_trace2(    Database _this,    Level level,    String methodName,    Transaction txn,    CursorConfig config){
      this._this=_this;
      this.level=level;
      this.methodName=methodName;
      this.txn=txn;
      this.config=config;
    }
    void execute() throws DatabaseException {
    }
    protected Database _this;
    protected Level level;
    protected String methodName;
    protected Transaction txn;
    protected CursorConfig config;
    protected StringBuffer sb;
  }
@MethodObject static class Database_trace {
    Database_trace(    Database _this,    Level level,    String methodName,    Transaction txn,    DatabaseEntry key,    DatabaseEntry data,    LockMode lockMode){
      this._this=_this;
      this.level=level;
      this.methodName=methodName;
      this.txn=txn;
      this.key=key;
      this.data=data;
      this.lockMode=lockMode;
    }
    void execute() throws DatabaseException {
    }
    protected Database _this;
    protected Level level;
    protected String methodName;
    protected Transaction txn;
    protected DatabaseEntry key;
    protected DatabaseEntry data;
    protected LockMode lockMode;
    protected StringBuffer sb;
  }
}
