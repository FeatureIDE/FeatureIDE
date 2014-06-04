package com.sleepycat.je;
public class JoinCursor {
  protected void hook62(  LockMode lockMode) throws DatabaseException {
    priCursor.trace(Level.FINEST,"JoinCursor.getNext(key): ",lockMode);
    original(lockMode);
  }
  protected void hook63(  LockMode lockMode) throws DatabaseException {
    priCursor.trace(Level.FINEST,"JoinCursor.getNext(key,data): ",lockMode);
    original(lockMode);
  }
}
