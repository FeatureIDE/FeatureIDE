package com.sleepycat.je.recovery;
public class RecoveryManager {
  protected void hook556() throws DatabaseException, IOException {
    env.enableDebugLoggingToDbLog();
    original();
  }
  /** 
 * Find the end of the log, initialize the FileManager. While we're perusing
 * the log, return the last checkpoint LSN if we happen to see it.
 */
  private void findEndOfLog(  boolean readOnly) throws IOException, DatabaseException {
    original(readOnly);
    env.enableDebugLoggingToDbLog();
  }
}
