package com.sleepycat.je;
public class Cursor {
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  void trace(  Level level,  String methodName,  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode){
    new Cursor_trace(this,level,methodName,key,data,lockMode).execute();
  }
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  void trace(  Level level,  String methodName,  LockMode lockMode){
    new Cursor_trace2(this,level,methodName,lockMode).execute();
  }
  protected void hook0() throws DatabaseException {
    trace(Level.FINEST,"Cursor.count: ",null);
    original();
  }
  protected void hook1() throws DatabaseException {
    trace(Level.FINEST,"Cursor.delete: ",null);
    original();
  }
  protected void hook2(  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    trace(Level.FINEST,"Cursor.put: ",key,data,null);
    original(key,data);
  }
  protected void hook3(  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    trace(Level.FINEST,"Cursor.putNoOverwrite: ",key,data,null);
    original(key,data);
  }
  protected void hook4(  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    trace(Level.FINEST,"Cursor.putNoDupData: ",key,data,null);
    original(key,data);
  }
  protected void hook5(  DatabaseEntry data) throws DatabaseException {
    trace(Level.FINEST,"Cursor.putCurrent: ",null,data,null);
    original(data);
  }
  protected void hook6(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getCurrent: ",lockMode);
    original(lockMode);
  }
  protected void hook7(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getFirst: ",lockMode);
    original(lockMode);
  }
  protected void hook8(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getLast: ",lockMode);
    original(lockMode);
  }
  protected void hook9(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getNext: ",lockMode);
    original(lockMode);
  }
  protected void hook10(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getNextDup: ",lockMode);
    original(lockMode);
  }
  protected void hook11(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getNextNoDup: ",lockMode);
    original(lockMode);
  }
  protected void hook12(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getPrev: ",lockMode);
    original(lockMode);
  }
  protected void hook13(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getPrevDup: ",lockMode);
    original(lockMode);
  }
  protected void hook14(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getPrevNoDup: ",lockMode);
    original(lockMode);
  }
  protected void hook15(  DatabaseEntry key,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getSearchKey: ",key,null,lockMode);
    original(key,lockMode);
  }
  protected void hook16(  DatabaseEntry key,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getSearchKeyRange: ",key,null,lockMode);
    original(key,lockMode);
  }
  protected void hook17(  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getSearchBoth: ",key,data,lockMode);
    original(key,data,lockMode);
  }
  protected void hook18(  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"Cursor.getSearchBothRange: ",key,data,lockMode);
    original(key,data,lockMode);
  }
@MethodObject static class Cursor_trace2 {
    Cursor_trace2(    Cursor _this,    Level level,    String methodName,    LockMode lockMode){
      this._this=_this;
      this.level=level;
      this.methodName=methodName;
      this.lockMode=lockMode;
    }
    void execute(){
    }
    protected Cursor _this;
    protected Level level;
    protected String methodName;
    protected LockMode lockMode;
    protected StringBuffer sb;
  }
@MethodObject static class Cursor_trace {
    Cursor_trace(    Cursor _this,    Level level,    String methodName,    DatabaseEntry key,    DatabaseEntry data,    LockMode lockMode){
      this._this=_this;
      this.level=level;
      this.methodName=methodName;
      this.key=key;
      this.data=data;
      this.lockMode=lockMode;
    }
    void execute(){
    }
    protected Cursor _this;
    protected Level level;
    protected String methodName;
    protected DatabaseEntry key;
    protected DatabaseEntry data;
    protected LockMode lockMode;
    protected StringBuffer sb;
  }
}
