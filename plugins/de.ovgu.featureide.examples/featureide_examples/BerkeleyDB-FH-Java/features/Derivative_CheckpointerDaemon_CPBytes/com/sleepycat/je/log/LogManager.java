package com.sleepycat.je.log;
abstract public class LogManager {
  private CheckpointMonitor checkpointMonitor;
  protected void hook498(  EnvironmentImpl envImpl) throws DatabaseException {
    checkpointMonitor=new CheckpointMonitor(envImpl);
    original(envImpl);
  }
  protected void hook499(  LogResult logResult) throws DatabaseException {
    if (logResult.wakeupCheckpointer) {
      checkpointMonitor.activate();
    }
    original(logResult);
  }
  protected boolean hook500(  LoggableObject item,  int entrySize,  boolean wakeupCheckpointer) throws IOException, DatabaseException {
    wakeupCheckpointer=checkpointMonitor.recordLogWrite(entrySize,item);
    return original(item,entrySize,wakeupCheckpointer);
  }
}
