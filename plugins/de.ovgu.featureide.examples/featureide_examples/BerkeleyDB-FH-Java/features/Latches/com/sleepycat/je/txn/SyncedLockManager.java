package com.sleepycat.je.txn;
public class SyncedLockManager {
  protected void hook782(  Long nodeId,  Locker locker,  LockType type,  boolean nonBlockingRequest,  int lockTableIndex) throws DatabaseException {
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,locker,type,nonBlockingRequest,lockTableIndex);
    }
  }
  protected void hook783(  String lockOrTxn,  Locker locker,  long nodeId,  LockType type,  LockGrantType grantType,  Lock useLock,  long timeout,  long start,  long now,  DatabaseImpl database,  int lockTableIndex){
synchronized (lockTableLatches[lockTableIndex]) {
      original(lockOrTxn,locker,nodeId,type,grantType,useLock,timeout,start,now,database,lockTableIndex);
    }
  }
  protected void hook784(  long nodeId,  Lock lock,  Locker locker,  boolean removeFromLocker,  int lockTableIndex) throws DatabaseException {
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,lock,locker,removeFromLocker,lockTableIndex);
    }
  }
  protected void hook785(  long nodeId,  Locker owningLocker,  Locker destLocker,  boolean demoteToRead,  int lockTableIndex) throws DatabaseException {
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,owningLocker,destLocker,demoteToRead,lockTableIndex);
    }
  }
  protected void hook786(  long nodeId,  Locker owningLocker,  Locker[] destLockers,  int lockTableIndex) throws DatabaseException {
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,owningLocker,destLockers,lockTableIndex);
    }
  }
  protected void hook787(  long nodeId,  Locker locker,  int lockTableIndex) throws DatabaseException {
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,locker,lockTableIndex);
    }
  }
  protected void hook788(  Long nodeId,  int lockTableIndex){
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,lockTableIndex);
    }
  }
  protected void hook789(  Long nodeId,  Locker locker,  LockType type,  int lockTableIndex){
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,locker,type,lockTableIndex);
    }
  }
  protected void hook790(  Long nodeId,  Locker locker,  int lockTableIndex){
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,locker,lockTableIndex);
    }
  }
  protected void hook791(  Long nodeId,  int lockTableIndex){
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,lockTableIndex);
    }
  }
  protected void hook792(  Long nodeId,  int lockTableIndex){
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,lockTableIndex);
    }
  }
  protected void hook793(  Long nodeId,  int lockTableIndex) throws DatabaseException {
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,lockTableIndex);
    }
  }
  protected void hook794(  Long nodeId,  Locker locker,  LockType type,  boolean flushFromWaiters,  MemoryBudget mb,  int lockTableIndex) throws DatabaseException {
synchronized (lockTableLatches[lockTableIndex]) {
      original(nodeId,locker,type,flushFromWaiters,mb,lockTableIndex);
    }
  }
  protected void hook795(  LockStats stats,  int i) throws DatabaseException {
synchronized (lockTableLatches[i]) {
      original(stats,i);
    }
  }
}
