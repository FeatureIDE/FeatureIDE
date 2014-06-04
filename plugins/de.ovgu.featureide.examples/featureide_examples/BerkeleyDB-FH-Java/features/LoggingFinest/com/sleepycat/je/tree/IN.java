package com.sleepycat.je.tree;
public class IN {
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  private void traceDelete(  Level level,  int index){
    new IN_traceDelete(this,level,index).execute();
  }
@MethodObject static class IN_traceDelete {
    IN_traceDelete(    IN _this,    Level level,    int index){
      this._this=_this;
      this.level=level;
      this.index=index;
    }
    void execute(){
    }
    protected IN _this;
    protected Level level;
    protected int index;
    protected Logger logger;
    protected StringBuffer sb;
  }
@MethodObject static class IN_deleteEntry {
    protected void hook616() throws DatabaseException {
      _this.traceDelete(Level.FINEST,index);
      original();
    }
  }
}
