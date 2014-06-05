/** 
 */
package com.sleepycat.je.dbi;
import java.io.PrintStream;
import java.util.HashSet;
import java.util.Set;
import com.sleepycat.je.BtreeStats;
import com.sleepycat.je.DatabaseStats;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.DBIN;
import com.sleepycat.je.tree.DIN;
import com.sleepycat.je.tree.DupCountLN;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.Node;
import com.sleepycat.je.tree.TreeWalkerStatsAccumulator;
import de.ovgu.cide.jakutil.*;
class StatsAccumulator implements TreeWalkerStatsAccumulator {
  private Set inNodeIdsSeen=new HashSet();
  private Set binNodeIdsSeen=new HashSet();
  private Set dinNodeIdsSeen=new HashSet();
  private Set dbinNodeIdsSeen=new HashSet();
  private Set dupCountLNsSeen=new HashSet();
  private long[] insSeenByLevel=null;
  private long[] binsSeenByLevel=null;
  private long[] dinsSeenByLevel=null;
  private long[] dbinsSeenByLevel=null;
  private long lnCount=0;
  private long deletedLNCount=0;
  private int mainTreeMaxDepth=0;
  private int duplicateTreeMaxDepth=0;
  private DatabaseStats useStats;
  PrintStream progressStream;
  int progressInterval;
  private static final int MAX_LEVELS=100;
  StatsAccumulator(  PrintStream progressStream,  int progressInterval,  DatabaseStats useStats){
    this.progressStream=progressStream;
    this.progressInterval=progressInterval;
    insSeenByLevel=new long[MAX_LEVELS];
    binsSeenByLevel=new long[MAX_LEVELS];
    dinsSeenByLevel=new long[MAX_LEVELS];
    dbinsSeenByLevel=new long[MAX_LEVELS];
    this.useStats=useStats;
  }
  public void processIN(  IN node,  Long nid,  int level){
    if (inNodeIdsSeen.add(nid)) {
      tallyLevel(level,insSeenByLevel);
      this.hook363(node);
    }
  }
  public void processBIN(  BIN node,  Long nid,  int level){
    if (binNodeIdsSeen.add(nid)) {
      tallyLevel(level,binsSeenByLevel);
      this.hook364(node);
    }
  }
  public void processDIN(  DIN node,  Long nid,  int level){
    if (dinNodeIdsSeen.add(nid)) {
      tallyLevel(level,dinsSeenByLevel);
      this.hook365(node);
    }
  }
  public void processDBIN(  DBIN node,  Long nid,  int level){
    if (dbinNodeIdsSeen.add(nid)) {
      tallyLevel(level,dbinsSeenByLevel);
      this.hook366(node);
    }
  }
  public void processDupCountLN(  DupCountLN node,  Long nid){
    dupCountLNsSeen.add(nid);
    this.hook367(node);
  }
  private void tallyLevel(  int levelArg,  long[] nodesSeenByLevel){
    int level=levelArg;
    if (level >= IN.DBMAP_LEVEL) {
      return;
    }
    if (level >= IN.MAIN_LEVEL) {
      level&=~IN.MAIN_LEVEL;
      if (level > mainTreeMaxDepth) {
        mainTreeMaxDepth=level;
      }
    }
 else {
      if (level > duplicateTreeMaxDepth) {
        duplicateTreeMaxDepth=level;
      }
    }
    nodesSeenByLevel[level]++;
  }
  public void incrementLNCount(){
    lnCount++;
    if (progressInterval != 0) {
      if ((lnCount % progressInterval) == 0) {
        copyToStats(useStats);
        progressStream.println(useStats);
      }
    }
  }
  public void incrementDeletedLNCount(){
    deletedLNCount++;
  }
  Set getINNodeIdsSeen(){
    return inNodeIdsSeen;
  }
  Set getBINNodeIdsSeen(){
    return binNodeIdsSeen;
  }
  Set getDINNodeIdsSeen(){
    return dinNodeIdsSeen;
  }
  Set getDBINNodeIdsSeen(){
    return dbinNodeIdsSeen;
  }
  long[] getINsByLevel(){
    return insSeenByLevel;
  }
  long[] getBINsByLevel(){
    return binsSeenByLevel;
  }
  long[] getDINsByLevel(){
    return dinsSeenByLevel;
  }
  long[] getDBINsByLevel(){
    return dbinsSeenByLevel;
  }
  long getLNCount(){
    return lnCount;
  }
  Set getDupCountLNCount(){
    return dupCountLNsSeen;
  }
  long getDeletedLNCount(){
    return deletedLNCount;
  }
  int getMainTreeMaxDepth(){
    return mainTreeMaxDepth;
  }
  int getDuplicateTreeMaxDepth(){
    return duplicateTreeMaxDepth;
  }
  void copyToStats(  DatabaseStats stats){
    BtreeStats bStats=(BtreeStats)stats;
    bStats.setInternalNodeCount(getINNodeIdsSeen().size());
    bStats.setBottomInternalNodeCount(getBINNodeIdsSeen().size());
    bStats.setDuplicateInternalNodeCount(getDINNodeIdsSeen().size());
    bStats.setDuplicateBottomInternalNodeCount(getDBINNodeIdsSeen().size());
    bStats.setLeafNodeCount(getLNCount());
    bStats.setDeletedLeafNodeCount(getDeletedLNCount());
    bStats.setDupCountLeafNodeCount(getDupCountLNCount().size());
    bStats.setMainTreeMaxDepth(getMainTreeMaxDepth());
    bStats.setDuplicateTreeMaxDepth(getDuplicateTreeMaxDepth());
    bStats.setINsByLevel(getINsByLevel());
    bStats.setBINsByLevel(getBINsByLevel());
    bStats.setDINsByLevel(getDINsByLevel());
    bStats.setDBINsByLevel(getDBINsByLevel());
  }
  protected void hook363(  IN node){
  }
  protected void hook364(  BIN node){
  }
  protected void hook365(  DIN node){
  }
  protected void hook366(  DBIN node){
  }
  protected void hook367(  DupCountLN node){
  }
}
