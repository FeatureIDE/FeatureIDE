package com.sleepycat.je.tree;
public class BIN {
  /** 
 * @Override
 */
  int getChildEvictionType(){
    Cleaner cleaner=getDatabase().getDbEnvironment().getCleaner();
    for (int i=0; i < getNEntries(); i++) {
      Node node=getTarget(i);
      if (node != null) {
        if (node instanceof LN) {
          if (cleaner.isEvictable(this,i)) {
            return MAY_EVICT_LNS;
          }
        }
 else {
          return MAY_NOT_EVICT;
        }
      }
    }
    return MAY_EVICT_NODE;
  }
  /** 
 * Reduce memory consumption by evicting all LN targets. Note that the
 * targets are not persistent, so this doesn't affect node dirtiness.
 * The BIN should be latched by the caller.
 * @return number of evicted bytes
 */
  public long evictLNs() throws DatabaseException {
    Cleaner cleaner=getDatabase().getDbEnvironment().getCleaner();
    long removed=0;
    if (nCursors() == 0) {
      for (int i=0; i < getNEntries(); i++) {
        removed+=evictInternal(i,cleaner);
      }
      this.hook601(removed);
    }
    return removed;
  }
  /** 
 * Evict a single LN if allowed and adjust the memory budget.
 */
  public void evictLN(  int index) throws DatabaseException {
    Cleaner cleaner=getDatabase().getDbEnvironment().getCleaner();
    long removed=evictInternal(index,cleaner);
    this.hook602(removed);
  }
  /** 
 * Evict a single LN if allowed. The amount of memory freed is returned and
 * must be subtracted from the memory budget by the caller.
 */
  private long evictInternal(  int index,  Cleaner cleaner) throws DatabaseException {
    Node n=getTarget(index);
    if (n instanceof LN && cleaner.isEvictable(this,index)) {
      setTarget(index,null);
      return n.getMemorySizeIncludedByParent();
    }
 else {
      return 0;
    }
  }
  protected void hook601(  long removed) throws DatabaseException {
  }
  protected void hook602(  long removed) throws DatabaseException {
  }
}
