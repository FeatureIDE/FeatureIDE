package com.sleepycat.je.tree;
public class IN {
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  private void traceSplit(  Level level,  IN parent,  IN newSibling,  long parentLsn,  long myNewLsn,  long newSiblingLsn,  int splitIndex,  int idKeyIndex,  int childIndex){
    new IN_traceSplit(this,level,parent,newSibling,parentLsn,myNewLsn,newSiblingLsn,splitIndex,idKeyIndex,childIndex).execute();
  }
@MethodObject static class IN_traceSplit {
    IN_traceSplit(    IN _this,    Level level,    IN parent,    IN newSibling,    long parentLsn,    long myNewLsn,    long newSiblingLsn,    int splitIndex,    int idKeyIndex,    int childIndex){
      this._this=_this;
      this.level=level;
      this.parent=parent;
      this.newSibling=newSibling;
      this.parentLsn=parentLsn;
      this.myNewLsn=myNewLsn;
      this.newSiblingLsn=newSiblingLsn;
      this.splitIndex=splitIndex;
      this.idKeyIndex=idKeyIndex;
      this.childIndex=childIndex;
    }
    void execute(){
    }
    protected IN _this;
    protected Level level;
    protected IN parent;
    protected IN newSibling;
    protected long parentLsn;
    protected long myNewLsn;
    protected long newSiblingLsn;
    protected int splitIndex;
    protected int idKeyIndex;
    protected int childIndex;
    protected Logger logger;
    protected StringBuffer sb;
  }
@MethodObject static class IN_splitInternal {
    protected void hook617() throws DatabaseException {
      _this.traceSplit(Level.FINE,parent,newSibling,parentLsn,myNewLsn,newSiblingLsn,splitIndex,idKeyIndex,childIndex);
      original();
    }
  }
}
