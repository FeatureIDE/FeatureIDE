package com.sleepycat.je.tree;
public final class Tree {
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  private void traceSplitRoot(  Level level,  String splitType,  IN newRoot,  long newRootLsn,  IN oldRoot,  long oldRootLsn){
    new Tree_traceSplitRoot(this,level,splitType,newRoot,newRootLsn,oldRoot,oldRootLsn).execute();
  }
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  private void traceMutate(  Level level,  BIN theBin,  LN existingLn,  LN newLn,  long newLsn,  DupCountLN dupCountLN,  long dupRootLsn,  DIN dupRoot,  long ddinLsn,  DBIN dupBin,  long dbinLsn){
    new Tree_traceMutate(this,level,theBin,existingLn,newLn,newLsn,dupCountLN,dupRootLsn,dupRoot,ddinLsn,dupBin,dbinLsn).execute();
  }
  protected void hook661() throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    RecoveryManager.traceRootDeletion(Level.FINE,database);
    original();
  }
  protected void hook662(  IN curRoot,  long curRootLsn,  long logLsn,  IN newRoot) throws DatabaseException {
    traceSplitRoot(Level.FINE,TRACE_ROOT_SPLIT,newRoot,logLsn,curRoot,curRootLsn);
    original(curRoot,curRootLsn,logLsn,newRoot);
  }
  protected void hook663(  DIN curRoot,  DIN newRoot,  long curRootLsn,  long logLsn) throws DatabaseException {
    traceSplitRoot(Level.FINE,TRACE_DUP_ROOT_SPLIT,newRoot,logLsn,curRoot,curRootLsn);
    original(curRoot,newRoot,curRootLsn,logLsn);
  }
  protected void hook664(  LN newLN,  DIN dupRoot,  DBIN dupBin,  BIN bin,  LN existingLN,  DupCountLN dupCountLN,  long dbinLsn,  long dinLsn,  long dupCountLsn,  long newLsn) throws DatabaseException {
    traceMutate(Level.FINE,bin,existingLN,newLN,newLsn,dupCountLN,dupCountLsn,dupRoot,dinLsn,dupBin,dbinLsn);
    original(newLN,dupRoot,dupBin,bin,existingLN,dupCountLN,dbinLsn,dinLsn,dupCountLsn,newLsn);
  }
  protected void hook665(  IN subtreeRoot) throws DatabaseException {
    Tracer.trace(Level.FINE,database.getDbEnvironment(),"SubtreeRemoval: subtreeRoot = " + subtreeRoot.getNodeId());
    original(subtreeRoot);
  }
@MethodObject static class Tree_traceMutate {
    Tree_traceMutate(    Tree _this,    Level level,    BIN theBin,    LN existingLn,    LN newLn,    long newLsn,    DupCountLN dupCountLN,    long dupRootLsn,    DIN dupRoot,    long ddinLsn,    DBIN dupBin,    long dbinLsn){
      this._this=_this;
      this.level=level;
      this.theBin=theBin;
      this.existingLn=existingLn;
      this.newLn=newLn;
      this.newLsn=newLsn;
      this.dupCountLN=dupCountLN;
      this.dupRootLsn=dupRootLsn;
      this.dupRoot=dupRoot;
      this.ddinLsn=ddinLsn;
      this.dupBin=dupBin;
      this.dbinLsn=dbinLsn;
    }
    void execute(){
    }
    protected Tree _this;
    protected Level level;
    protected BIN theBin;
    protected LN existingLn;
    protected LN newLn;
    protected long newLsn;
    protected DupCountLN dupCountLN;
    protected long dupRootLsn;
    protected DIN dupRoot;
    protected long ddinLsn;
    protected DBIN dupBin;
    protected long dbinLsn;
    protected Logger logger;
    protected StringBuffer sb;
  }
@MethodObject static class Tree_traceSplitRoot {
    Tree_traceSplitRoot(    Tree _this,    Level level,    String splitType,    IN newRoot,    long newRootLsn,    IN oldRoot,    long oldRootLsn){
      this._this=_this;
      this.level=level;
      this.splitType=splitType;
      this.newRoot=newRoot;
      this.newRootLsn=newRootLsn;
      this.oldRoot=oldRoot;
      this.oldRootLsn=oldRootLsn;
    }
    void execute(){
    }
    protected Tree _this;
    protected Level level;
    protected String splitType;
    protected IN newRoot;
    protected long newRootLsn;
    protected IN oldRoot;
    protected long oldRootLsn;
    protected Logger logger;
    protected StringBuffer sb;
  }
}
