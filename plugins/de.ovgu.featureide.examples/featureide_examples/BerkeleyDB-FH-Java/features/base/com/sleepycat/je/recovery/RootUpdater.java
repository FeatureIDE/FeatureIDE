/** 
 */
package com.sleepycat.je.recovery;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.tree.ChildReference;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.Tree;
import com.sleepycat.je.tree.WithRootLatched;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
class RootUpdater implements WithRootLatched {
  private Tree tree;
  private IN inFromLog;
  private long lsn=DbLsn.NULL_LSN;
  private boolean inserted=false;
  private boolean replaced=false;
  private long origLsn=DbLsn.NULL_LSN;
  RootUpdater(  Tree tree,  IN inFromLog,  long lsn){
    this.tree=tree;
    this.inFromLog=inFromLog;
    this.lsn=lsn;
  }
  public IN doWork(  ChildReference root) throws DatabaseException {
    ChildReference newRoot=tree.makeRootChildReference(inFromLog,new byte[0],lsn);
    this.hook600();
    if (root == null) {
      tree.setRoot(newRoot,false);
      inserted=true;
    }
 else {
      origLsn=root.getLsn();
      if (DbLsn.compareTo(origLsn,lsn) < 0) {
        tree.setRoot(newRoot,false);
        replaced=true;
      }
    }
    return null;
  }
  boolean updateDone(){
    return inserted || replaced;
  }
  boolean getInserted(){
    return inserted;
  }
  boolean getReplaced(){
    return replaced;
  }
  long getOriginalLsn(){
    return origLsn;
  }
  protected void hook600() throws DatabaseException {
  }
}
