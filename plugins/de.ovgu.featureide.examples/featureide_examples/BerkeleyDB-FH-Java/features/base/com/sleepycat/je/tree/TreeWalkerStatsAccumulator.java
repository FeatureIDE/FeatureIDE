package com.sleepycat.je.tree;
import de.ovgu.cide.jakutil.*;
/** 
 * Accumulates stats about a tree during tree walking.
 */
public interface TreeWalkerStatsAccumulator {
  public void processIN(  IN node,  Long nid,  int level);
  public void processBIN(  BIN node,  Long nid,  int level);
  public void processDIN(  DIN node,  Long nid,  int level);
  public void processDBIN(  DBIN node,  Long nid,  int level);
  public void processDupCountLN(  DupCountLN node,  Long nid);
  public void incrementLNCount();
  public void incrementDeletedLNCount();
}
