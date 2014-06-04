package com.sleepycat.je.log;
import com.sleepycat.je.EnvironmentStats;
import com.sleepycat.je.StatsConfig;
class LogBufferPool {
  private long nNotResident=0;
  private long nCacheMiss=0;
  void loadStats(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
    stats.setNCacheMiss(nCacheMiss);
    stats.setNNotResident(nNotResident);
    if (config.getClear()) {
      nCacheMiss=0;
      nNotResident=0;
    }
    this.hook484();
    long bufferBytes=0;
    int nLogBuffers=0;
    this.hook483(bufferBytes,nLogBuffers);
    stats.setNLogBuffers(nLogBuffers);
    stats.setBufferBytes(bufferBytes);
  }
  protected void hook483(  long bufferBytes,  int nLogBuffers) throws DatabaseException {
    Iterator iter=bufferPool.iterator();
    while (iter.hasNext()) {
      LogBuffer l=(LogBuffer)iter.next();
      nLogBuffers++;
      bufferBytes+=l.getCapacity();
    }
  }
  protected void hook484() throws DatabaseException {
  }
  protected LogBuffer hook489(  long lsn,  LogBuffer foundBuffer) throws DatabaseException {
    nNotResident++;
    return original(lsn,foundBuffer);
  }
  protected void hook496() throws DatabaseException {
    nCacheMiss++;
    original();
  }
}
