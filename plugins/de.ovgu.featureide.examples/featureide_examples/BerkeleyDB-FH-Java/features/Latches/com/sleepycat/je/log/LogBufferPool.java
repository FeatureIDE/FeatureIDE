package com.sleepycat.je.log;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
class LogBufferPool {
  private Latch bufferPoolLatch;
  protected void hook485(  EnvironmentImpl envImpl) throws DatabaseException {
    bufferPoolLatch=LatchSupport.makeLatch(DEBUG_NAME + "_FullLatch",envImpl);
    original(envImpl);
  }
  /** 
 * Initialize the pool at construction time and when the cache is resized.
 * This method is called after the memory budget has been calculated.
 */
  void reset(  DbConfigManager configManager) throws DatabaseException {
    original(configManager);
    bufferPoolLatch.release();
  }
  protected void hook486() throws DatabaseException {
    bufferPoolLatch.acquire();
    original();
  }
  protected void hook487(  int bufferSize,  LogBuffer latchedBuffer) throws IOException, DatabaseException {
    try {
      original(bufferSize,latchedBuffer);
    }
  finally {
      if (latchedBuffer != null) {
        latchedBuffer.release();
      }
    }
  }
  protected void hook488() throws IOException, DatabaseException {
    currentWriteBuffer.latchForWrite();
    original();
  }
  protected LogBuffer hook489(  long lsn,  LogBuffer foundBuffer) throws DatabaseException {
    bufferPoolLatch.acquire();
    try {
      foundBuffer=original(lsn,foundBuffer);
    }
  finally {
      bufferPoolLatch.releaseIfOwner();
    }
    return foundBuffer;
  }
  protected void hook490() throws IOException, DatabaseException {
    bufferPoolLatch.release();
    original();
  }
  protected void hook491() throws IOException, DatabaseException {
    bufferPoolLatch.acquire();
    original();
  }
  protected void hook492(  LogBuffer latchedBuffer) throws IOException, DatabaseException {
    latchedBuffer.release();
    original(latchedBuffer);
  }
  protected void hook493(  LogBuffer nextToUse) throws IOException, DatabaseException {
    try {
      original(nextToUse);
    }
  finally {
      bufferPoolLatch.releaseIfOwner();
    }
  }
  protected void hook494(  LogBuffer latchedBuffer) throws IOException, DatabaseException {
    latchedBuffer.release();
    original(latchedBuffer);
  }
  protected void hook495() throws IOException, DatabaseException {
    bufferPoolLatch.acquire();
    original();
  }
}
