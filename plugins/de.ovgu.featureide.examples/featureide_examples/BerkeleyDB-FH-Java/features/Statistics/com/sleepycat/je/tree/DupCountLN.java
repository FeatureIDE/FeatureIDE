package com.sleepycat.je.tree;
public final class DupCountLN {
  public void accumulateStats(  TreeWalkerStatsAccumulator acc){
    acc.processDupCountLN(this,new Long(getNodeId()));
  }
}
