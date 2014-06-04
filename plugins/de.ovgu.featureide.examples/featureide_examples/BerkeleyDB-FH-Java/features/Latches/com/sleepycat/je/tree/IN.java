package com.sleepycat.je.tree;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchNotHeldException;
import com.sleepycat.je.latch.LatchSupport;
public class IN {
  private Latch latch;
  /** 
 * Latch this node and set the generation.
 */
  public void latch() throws DatabaseException {
    latch(true);
  }
  /** 
 * Latch this node if it is not latched by another thread, and set the
 * generation if the latch succeeds.
 */
  public boolean latchNoWait() throws DatabaseException {
    return latchNoWait(true);
  }
  /** 
 * Release the latch on this node.
 */
  public void releaseLatch() throws LatchNotHeldException {
    latch.release();
  }
  /** 
 * Release the latch on this node.
 */
  public void releaseLatchIfOwner() throws LatchNotHeldException {
    latch.releaseIfOwner();
  }
  /** 
 * @return true if this thread holds the IN's latch
 */
  public boolean isLatchOwner(){
    return latch.isOwner();
  }
  protected void hook618(  EnvironmentImpl env){
    latch=LatchSupport.makeLatch(shortClassName() + getNodeId(),env);
    original(env);
  }
  /** 
 * Latch this node, optionally setting the generation.
 */
  public void latch(  boolean updateGeneration) throws DatabaseException {
    original(updateGeneration);
    latch.acquire();
  }
  protected void hook619(  boolean updateGeneration) throws DatabaseException {
    if (latch.acquireNoWait()) {
      original(updateGeneration);
    }
 else {
      throw new ReturnBoolean(false);
    }
  }
  /** 
 * See if you are the parent of this child. If not, find a child of your's
 * that may be the parent, and return it. If there are no possiblities,
 * return null. Note that the keys of the target are passed in so we don't
 * have to latch the target to look at them. Also, this node is latched
 * upon entry.
 * @param doFetch If true, fetch the child in the pursuit of this search.
 * If false, give up if the child is not resident. In that case, we have
 * a potential ancestor, but are not sure if this is the parent.
 */
  void findParent(  Tree.SearchType searchType,  long targetNodeId,  boolean targetContainsDuplicates,  boolean targetIsRoot,  byte[] targetMainTreeKey,  byte[] targetDupTreeKey,  SearchResult result,  boolean requireExactMatch,  boolean updateGeneration,  int targetLevel,  List trackingList,  boolean doFetch) throws DatabaseException {
    assert isLatchOwner();
    original(searchType,targetNodeId,targetContainsDuplicates,targetIsRoot,targetMainTreeKey,targetDupTreeKey,result,requireExactMatch,updateGeneration,targetLevel,trackingList,doFetch);
  }
  protected void hook620() throws DatabaseException {
    releaseLatch();
    original();
  }
  protected void hook621() throws DatabaseException {
    releaseLatch();
    original();
  }
  protected void hook622() throws DatabaseException {
    releaseLatch();
    original();
  }
  protected void hook623() throws DatabaseException {
    releaseLatch();
    original();
  }
  protected void hook624() throws DatabaseException {
    releaseLatch();
    original();
  }
  protected void hook625(  Node child) throws DatabaseException {
    ((IN)child).releaseLatch();
    original(child);
  }
  protected void hook626() throws DatabaseException {
    releaseLatch();
    original();
  }
  protected void hook627() throws DatabaseException {
    releaseLatch();
    original();
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion) throws LogException {
    original(itemBuffer,entryTypeVersion);
    latch.setName(shortClassName() + getNodeId());
  }
@MethodObject static class IN_splitInternal {
    protected void hook630() throws DatabaseException {
      try {
        original();
      }
  finally {
        newSibling.releaseLatch();
      }
    }
    protected void hook631() throws DatabaseException {
      newSibling.latch();
      original();
    }
  }
@MethodObject static class IN_isValidForDelete {
    protected void hook634() throws DatabaseException {
      needToLatch=!_this.isLatchOwner();
      try {
        original();
      }
  finally {
        if (needToLatch) {
          _this.releaseLatchIfOwner();
        }
      }
    }
    protected void hook635() throws DatabaseException {
      if (needToLatch) {
        _this.latch();
      }
      original();
    }
  }
@MethodObject static class IN_validateSubtreeBeforeDelete {
    protected void hook628() throws DatabaseException {
      needToLatch=!_this.isLatchOwner();
      try {
        original();
      }
  finally {
        if (needToLatch) {
          _this.releaseLatchIfOwner();
        }
      }
    }
    protected void hook629() throws DatabaseException {
      if (needToLatch) {
        _this.latch();
      }
      original();
    }
  }
@MethodObject static class IN_verify {
    void execute() throws DatabaseException {
      unlatchThis=false;
      original();
    }
    protected void hook632() throws DatabaseException {
      if (!_this.isLatchOwner()) {
        _this.latch();
        unlatchThis=true;
      }
      original();
    }
    protected void hook633() throws DatabaseException {
      if (unlatchThis) {
        _this.releaseLatch();
      }
      original();
    }
  }
}
