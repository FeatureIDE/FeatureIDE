package com.sleepycat.je.tree;
public class LN {
  /** 
 * Compute the approximate size of this node in memory for evictor
 * invocation purposes.
 */
  public long getMemorySizeIncludedByParent(){
    int size=MemoryBudget.LN_OVERHEAD;
    if (data != null) {
      size+=MemoryBudget.byteArraySize(data.length);
    }
    return size;
  }
}
