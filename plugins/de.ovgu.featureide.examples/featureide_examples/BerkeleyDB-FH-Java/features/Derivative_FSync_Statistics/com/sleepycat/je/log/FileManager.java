package com.sleepycat.je.log;
public class FileManager {
  public long getNFSyncs(){
    return syncManager.getNFSyncs();
  }
  public long getNFSyncRequests(){
    return syncManager.getNFSyncRequests();
  }
  public long getNFSyncTimeouts(){
    return syncManager.getNTimeouts();
  }
  void loadStats(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
    syncManager.loadStats(config,stats);
  }
}
