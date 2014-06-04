package com.sleepycat.je.log;
import com.sleepycat.je.EnvironmentStats;
import com.sleepycat.je.StatsConfig;
class FSyncManager {
  private long nFSyncRequests=0;
  private long nFSyncs=0;
  private long nTimeouts=0;
  long getNFSyncRequests(){
    return nFSyncRequests;
  }
  long getNFSyncs(){
    return nFSyncs;
  }
  long getNTimeouts(){
    return nTimeouts;
  }
  void loadStats(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
    stats.setNFSyncs(nFSyncs);
    stats.setNFSyncRequests(nFSyncRequests);
    stats.setNFSyncTimeouts(nTimeouts);
    if (config.getClear()) {
      nFSyncs=0;
      nFSyncRequests=0;
      nTimeouts=0;
    }
  }
  protected void hook435() throws DatabaseException {
    nFSyncRequests++;
    original();
  }
  protected void hook436() throws DatabaseException {
synchronized (this) {
      nTimeouts++;
    }
    original();
  }
  protected void hook437() throws DatabaseException {
    nFSyncs++;
    original();
  }
}
