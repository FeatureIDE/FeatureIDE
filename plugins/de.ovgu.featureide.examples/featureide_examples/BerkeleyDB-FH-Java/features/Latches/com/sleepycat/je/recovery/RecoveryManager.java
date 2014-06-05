package com.sleepycat.je.recovery;
import com.sleepycat.je.latch.LatchSupport;
public class RecoveryManager {
  protected void hook585(  IN in) throws DatabaseException {
    in.latch();
    original(in);
  }
  protected void hook586(  RecoveryInfo info,  LNFileReader reader,  TreeLocation location,  LN ln,  long logLsn,  long abortLsn,  boolean abortKnownDeleted,  DatabaseImpl db) throws IOException, DatabaseException, Exception {
    try {
      original(info,reader,location,ln,logLsn,abortLsn,abortKnownDeleted,db);
    }
  finally {
      if (location.bin != null) {
        location.bin.releaseLatchIfOwner();
      }
    }
  }
  protected void hook587(  IN inFromLog,  long logLsn) throws DatabaseException {
    inFromLog.releaseLatchIfOwner();
    assert (LatchSupport.countLatchesHeld() == 0) : LatchSupport.latchesHeldToString() + "LSN = " + DbLsn.toString(logLsn)+ " inFromLog = "+ inFromLog.getNodeId();
    original(inFromLog,logLsn);
  }
  protected void hook588(  SearchResult result) throws DatabaseException {
    if (result.parent != null) {
      result.parent.releaseLatch();
    }
    original(result);
  }
  protected void hook589(  IN parent) throws DatabaseException {
    if (parent != null) {
      parent.releaseLatch();
    }
    original(parent);
  }
  protected void hook590(  SearchResult result) throws DatabaseException {
    if (result.parent != null) {
      result.parent.releaseLatch();
    }
    original(result);
  }
  protected void hook591(  TreeLocation location) throws DatabaseException {
    if (location.bin != null) {
      location.bin.releaseLatchIfOwner();
    }
    original(location);
  }
  protected static boolean hook592(  TreeLocation location,  long logLsn,  long abortLsn,  boolean replaced,  DIN duplicateRoot) throws DatabaseException {
    duplicateRoot.latch();
    try {
      replaced=original(location,logLsn,abortLsn,replaced,duplicateRoot);
    }
  finally {
      duplicateRoot.releaseLatch();
    }
    return replaced;
  }
}
