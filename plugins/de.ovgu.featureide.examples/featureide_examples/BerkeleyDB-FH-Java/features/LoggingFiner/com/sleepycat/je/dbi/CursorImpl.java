package com.sleepycat.je.dbi;
public class CursorImpl {
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  private void trace(  Level level,  String changeType,  BIN theBin,  LN ln,  int lnIndex,  long oldLsn,  long newLsn){
    new CursorImpl_trace(this,level,changeType,theBin,ln,lnIndex,oldLsn,newLsn).execute();
  }
  protected void hook204(  LN ln,  long oldLsn,  long newLsn) throws DatabaseException {
    trace(Level.FINER,TRACE_DELETE,targetBin,ln,targetIndex,oldLsn,newLsn);
    original(ln,oldLsn,newLsn);
  }
  protected void hook205(  LN ln,  long oldLsn,  long newLsn) throws DatabaseException {
    trace(Level.FINER,TRACE_MOD,targetBin,ln,targetIndex,oldLsn,newLsn);
    original(ln,oldLsn,newLsn);
  }
@MethodObject static class CursorImpl_trace {
    CursorImpl_trace(    CursorImpl _this,    Level level,    String changeType,    BIN theBin,    LN ln,    int lnIndex,    long oldLsn,    long newLsn){
      this._this=_this;
      this.level=level;
      this.changeType=changeType;
      this.theBin=theBin;
      this.ln=ln;
      this.lnIndex=lnIndex;
      this.oldLsn=oldLsn;
      this.newLsn=newLsn;
    }
    void execute(){
    }
    protected CursorImpl _this;
    protected Level level;
    protected String changeType;
    protected BIN theBin;
    protected LN ln;
    protected int lnIndex;
    protected long oldLsn;
    protected long newLsn;
    protected Logger logger;
    protected StringBuffer sb;
  }
}
