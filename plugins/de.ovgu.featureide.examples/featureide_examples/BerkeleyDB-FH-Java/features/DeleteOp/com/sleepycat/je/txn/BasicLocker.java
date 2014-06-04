package com.sleepycat.je.txn;
public class BasicLocker {
  public void markDeleteAtTxnEnd(  DatabaseImpl db,  boolean deleteAtCommit) throws DatabaseException {
    if (deleteAtCommit) {
      db.deleteAndReleaseINs();
    }
  }
}
