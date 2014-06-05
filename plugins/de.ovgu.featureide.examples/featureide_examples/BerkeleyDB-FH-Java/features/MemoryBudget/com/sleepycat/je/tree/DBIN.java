package com.sleepycat.je.tree;
public final class DBIN {
  /** 
 * Count up the memory usage attributable to this node alone.
 */
  protected long computeMemorySize(){
    long size=super.computeMemorySize();
    return size;
  }
  public static long computeOverhead(  DbConfigManager configManager) throws DatabaseException {
    return MemoryBudget.DBIN_FIXED_OVERHEAD + IN.computeArraysOverhead(configManager);
  }
  protected long getMemoryOverhead(  MemoryBudget mb){
    return mb.getDBINOverhead();
  }
}
