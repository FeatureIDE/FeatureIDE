package com.sleepycat.je.tree;
public final class Tree {
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  private void traceInsert(  Level level,  EnvironmentImpl env,  BIN insertingBin,  LN ln,  long lnLsn,  int index){
    new Tree_traceInsert(this,level,env,insertingBin,ln,lnLsn,index).execute();
  }
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  private void traceInsertDuplicate(  Level level,  EnvironmentImpl env,  BIN insertingDBin,  LN ln,  long lnLsn,  long binNid){
    new Tree_traceInsertDuplicate(this,level,env,insertingDBin,ln,lnLsn,binNid).execute();
  }
  protected void hook657(  LN ln,  EnvironmentImpl env,  BIN bin,  int index,  long newLsn) throws DatabaseException {
    traceInsert(Level.FINER,env,bin,ln,newLsn,index);
    original(ln,env,bin,index,newLsn);
  }
  protected void hook658(  LN ln,  EnvironmentImpl env,  BIN bin,  int index,  long newLsn) throws DatabaseException {
    traceInsert(Level.FINER,env,bin,ln,newLsn,index);
    original(ln,env,bin,index,newLsn);
  }
  protected void hook659(  LN newLN,  long binNid,  DBIN dupBin,  long newLsn) throws DatabaseException {
    traceInsertDuplicate(Level.FINER,database.getDbEnvironment(),dupBin,newLN,newLsn,binNid);
    original(newLN,binNid,dupBin,newLsn);
  }
  protected void hook660(  LN newLN,  long binNid,  DBIN dupBin,  long newLsn) throws DatabaseException {
    traceInsertDuplicate(Level.FINER,database.getDbEnvironment(),dupBin,newLN,newLsn,binNid);
    original(newLN,binNid,dupBin,newLsn);
  }
@MethodObject static class Tree_traceInsertDuplicate {
    Tree_traceInsertDuplicate(    Tree _this,    Level level,    EnvironmentImpl env,    BIN insertingDBin,    LN ln,    long lnLsn,    long binNid){
      this._this=_this;
      this.level=level;
      this.env=env;
      this.insertingDBin=insertingDBin;
      this.ln=ln;
      this.lnLsn=lnLsn;
      this.binNid=binNid;
    }
    void execute(){
    }
    protected Tree _this;
    protected Level level;
    protected EnvironmentImpl env;
    protected BIN insertingDBin;
    protected LN ln;
    protected long lnLsn;
    protected long binNid;
    protected Logger logger;
    protected StringBuffer sb;
  }
@MethodObject static class Tree_traceInsert {
    Tree_traceInsert(    Tree _this,    Level level,    EnvironmentImpl env,    BIN insertingBin,    LN ln,    long lnLsn,    int index){
      this._this=_this;
      this.level=level;
      this.env=env;
      this.insertingBin=insertingBin;
      this.ln=ln;
      this.lnLsn=lnLsn;
      this.index=index;
    }
    void execute(){
    }
    protected Tree _this;
    protected Level level;
    protected EnvironmentImpl env;
    protected BIN insertingBin;
    protected LN ln;
    protected long lnLsn;
    protected int index;
    protected Logger logger;
    protected StringBuffer sb;
  }
}
