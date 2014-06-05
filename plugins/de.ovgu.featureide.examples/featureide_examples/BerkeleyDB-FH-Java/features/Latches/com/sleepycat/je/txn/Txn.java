package com.sleepycat.je.txn;
public class Txn {
  protected void hook802(  long undoLsn,  TreeLocation location,  LNLogEntry undoEntry,  LN undoLN,  DatabaseImpl db,  long abortLsn,  boolean abortKnownDeleted) throws DatabaseException, RuntimeException {
    try {
      original(undoLsn,location,undoEntry,undoLN,db,abortLsn,abortKnownDeleted);
    }
  finally {
      if (location.bin != null) {
        location.bin.releaseLatchIfOwner();
      }
    }
  }
}
