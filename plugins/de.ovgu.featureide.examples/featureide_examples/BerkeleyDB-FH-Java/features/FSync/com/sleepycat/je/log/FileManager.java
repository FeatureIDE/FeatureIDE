package com.sleepycat.je.log;
public class FileManager {
  private FSyncManager syncManager;
  /** 
 * Flush a file using the group sync mechanism, trying to amortize off other
 * syncs.
 */
  void groupSync() throws DatabaseException {
    syncManager.fsync();
  }
  protected void hook452(  EnvironmentImpl envImpl) throws DatabaseException {
    syncManager=new FSyncManager(envImpl);
    original(envImpl);
  }
}
