package com.sleepycat.je.evictor;
import com.sleepycat.je.EnvironmentStats;
import com.sleepycat.je.StatsConfig;
public class Evictor {
  private int nEvictPasses=0;
  private long nNodesSelected=0;
  private long nNodesSelectedThisRun;
  private int nNodesScanned=0;
  private long nNodesEvicted=0;
  private long nNodesEvictedThisRun;
  private long nBINsStripped=0;
  private long nBINsStrippedThisRun;
  /** 
 * Load stats.
 */
  public void loadStats(  StatsConfig config,  EnvironmentStats stat) throws DatabaseException {
    stat.setNEvictPasses(nEvictPasses);
    stat.setNNodesSelected(nNodesSelected);
    stat.setNNodesScanned(nNodesScanned);
    stat.setNNodesExplicitlyEvicted(nNodesEvicted);
    stat.setNBINsStripped(nBINsStripped);
    stat.setRequiredEvictBytes(currentRequiredEvictBytes);
    if (config.getClear()) {
      nEvictPasses=0;
      nNodesSelected=0;
      nNodesScanned=0;
      nNodesEvicted=0;
      nBINsStripped=0;
    }
  }
  protected void hook380(  IN target) throws DatabaseException {
    if (target != null) {
      nNodesSelectedThisRun++;
      nNodesSelected++;
    }
    original(target);
  }
  protected void hook383(  long evictedBytes) throws DatabaseException {
    if (evictedBytes > 0) {
      nBINsStrippedThisRun++;
      nBINsStripped++;
    }
    original(evictedBytes);
  }
  protected void hook384() throws DatabaseException {
    nNodesEvictedThisRun++;
    nNodesEvicted++;
    original();
  }
@MethodObject static class Evictor_evictBatch {
    long execute() throws DatabaseException {
      _this.nNodesSelectedThisRun=0;
      _this.nNodesEvictedThisRun=0;
      return original();
    }
    protected void hook381() throws DatabaseException {
      _this.nBINsStrippedThisRun=0;
      _this.nEvictPasses++;
      original();
    }
    protected void hook382() throws DatabaseException {
      _this.nNodesScanned+=_this.nNodesScannedThisRun;
      original();
    }
  }
}
