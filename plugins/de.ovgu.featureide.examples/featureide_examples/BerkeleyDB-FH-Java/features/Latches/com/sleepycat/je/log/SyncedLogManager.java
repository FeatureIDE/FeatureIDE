package com.sleepycat.je.log;
public class SyncedLogManager {
  protected void hook511(  LoggableObject item,  boolean isProvisional,  boolean flushRequired,  boolean forceNewLogFile,  long oldNodeLsn,  boolean marshallOutsideLatch,  ByteBuffer marshalledBuffer,  UtilizationTracker tracker) throws IOException, DatabaseException {
synchronized (logWriteLatch) {
      original(item,isProvisional,flushRequired,forceNewLogFile,oldNodeLsn,marshallOutsideLatch,marshalledBuffer,tracker);
    }
  }
  protected void hook512() throws LogException, DatabaseException, IOException {
synchronized (logWriteLatch) {
      original();
    }
  }
  protected void hook513(  long file) throws DatabaseException {
synchronized (logWriteLatch) {
      original(file);
    }
  }
  protected void hook514(  long lsn,  LogEntryType type,  UtilizationTracker tracker) throws DatabaseException {
synchronized (logWriteLatch) {
      original(lsn,type,tracker);
    }
  }
  protected void hook515(  TrackedFileSummary[] summaries,  UtilizationTracker tracker) throws DatabaseException {
synchronized (logWriteLatch) {
      original(summaries,tracker);
    }
  }
  /** 
 * @see LogManager#countObsoleteINs
 */
  public void countObsoleteINs(  List lsnList) throws DatabaseException {
synchronized (logWriteLatch) {
      original(lsnList);
    }
  }
}
