package com.sleepycat.je.log;
class FileCache {
  protected void hook438(  Iterator iter,  boolean done,  Long evictId,  FileHandle evictTarget) throws DatabaseException {
    if (evictTarget.latchNoWait()) {
      original(iter,done,evictId,evictTarget);
    }
  }
  protected void hook439(  Iterator iter,  Long evictId,  FileHandle evictTarget) throws IOException, DatabaseException {
    try {
      original(iter,evictId,evictTarget);
    }
  finally {
      evictTarget.release();
    }
  }
  protected void hook440(  Iterator iter,  FileHandle fileHandle) throws IOException, DatabaseException {
    try {
      original(iter,fileHandle);
    }
  finally {
      fileHandle.release();
    }
  }
  protected void hook441(  FileHandle evictTarget) throws DatabaseException {
    evictTarget.release();
    original(evictTarget);
  }
  protected void hook442(  FileHandle evictTarget) throws IOException, DatabaseException {
    evictTarget.latch();
    original(evictTarget);
  }
  protected void hook443(  FileHandle fileHandle) throws IOException, DatabaseException {
    fileHandle.latch();
    original(fileHandle);
  }
}
