package com.sleepycat.je.tree;
public final class DupCountLN {
  /** 
 * Compute the approximate size of this node in memory for evictor
 * invocation purposes.
 */
  public long getMemorySizeIncludedByParent(){
    return MemoryBudget.DUPCOUNTLN_OVERHEAD;
  }
}
