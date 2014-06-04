package com.sleepycat.je;
public class SecondaryCursor {
  protected void hook65() throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.delete: ",null);
    original();
  }
  protected void hook66(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getCurrent: ",lockMode);
    original(lockMode);
  }
  protected void hook67(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getFirst: ",lockMode);
    original(lockMode);
  }
  protected void hook68(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getLast: ",lockMode);
    original(lockMode);
  }
  protected void hook69(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getNext: ",lockMode);
    original(lockMode);
  }
  protected void hook70(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getNextDup: ",lockMode);
    original(lockMode);
  }
  protected void hook71(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getNextNoDup: ",null,null,lockMode);
    original(lockMode);
  }
  protected void hook72(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getPrev: ",lockMode);
    original(lockMode);
  }
  protected void hook73(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getPrevDup: ",lockMode);
    original(lockMode);
  }
  protected void hook74(  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getPrevNoDup: ",lockMode);
    original(lockMode);
  }
  protected void hook75(  DatabaseEntry key,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getSearchKey: ",key,null,lockMode);
    original(key,lockMode);
  }
  protected void hook76(  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getSearchKeyRange: ",key,data,lockMode);
    original(key,data,lockMode);
  }
  protected void hook77(  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getSearchBoth: ",key,data,lockMode);
    original(key,data,lockMode);
  }
  protected void hook78(  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    trace(Level.FINEST,"SecondaryCursor.getSearchBothRange: ",key,data,lockMode);
    original(key,data,lockMode);
  }
}
