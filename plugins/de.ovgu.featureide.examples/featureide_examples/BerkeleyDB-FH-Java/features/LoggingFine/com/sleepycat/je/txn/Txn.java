package com.sleepycat.je.txn;
public class Txn {
  protected void hook799(  int numReadLocks,  int numWriteLocks,  boolean openCursors) throws DatabaseException {
    Tracer.trace(Level.FINE,envImpl,"Abort:id = " + id + " numWriteLocks= "+ numWriteLocks+ " numReadLocks= "+ numReadLocks+ " openCursors= "+ openCursors);
    original(numReadLocks,numWriteLocks,openCursors);
  }
}
