/** 
 */
package com.sleepycat.je.recovery;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.log.LogManager;
import com.sleepycat.je.tree.ChildReference;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.WithRootLatched;
import de.ovgu.cide.jakutil.*;
class RootFlusher implements WithRootLatched {
  private DatabaseImpl db;
  private boolean flushed;
  private boolean stillRoot;
  private LogManager logManager;
  private long targetNodeId;
  RootFlusher(  DatabaseImpl db,  LogManager logManager,  long targetNodeId){
    this.db=db;
    flushed=false;
    this.logManager=logManager;
    this.targetNodeId=targetNodeId;
    stillRoot=false;
  }
  /** 
 * Flush the rootIN if dirty.
 */
  public IN doWork(  ChildReference root) throws DatabaseException {
    if (root == null) {
      return null;
    }
    IN rootIN=(IN)root.fetchTarget(db,null);
    this.hook599(root,rootIN);
    return null;
  }
  boolean getFlushed(){
    return flushed;
  }
  boolean stillRoot(){
    return stillRoot;
  }
  protected void hook599(  ChildReference root,  IN rootIN) throws DatabaseException {
    if (rootIN.getNodeId() == targetNodeId) {
      stillRoot=true;
      if (rootIN.getDirty()) {
        long newLsn=rootIN.log(logManager);
        root.setLsn(newLsn);
        flushed=true;
      }
    }
  }
}
