package com.sleepycat.je.tree;
public class BIN {
  public static long computeOverhead(  DbConfigManager configManager) throws DatabaseException {
    return MemoryBudget.BIN_FIXED_OVERHEAD + IN.computeArraysOverhead(configManager);
  }
  protected long getMemoryOverhead(  MemoryBudget mb){
    return mb.getBINOverhead();
  }
  protected void hook610(  int index){
    updateMemorySize(getTarget(index),null);
    original(index);
  }
}
