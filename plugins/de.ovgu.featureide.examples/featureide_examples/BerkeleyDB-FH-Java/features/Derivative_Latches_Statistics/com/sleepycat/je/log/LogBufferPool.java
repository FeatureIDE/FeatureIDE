package com.sleepycat.je.log;
class LogBufferPool {
  protected void hook483(  long bufferBytes,  int nLogBuffers) throws DatabaseException {
    try {
      original(bufferBytes,nLogBuffers);
    }
  finally {
      bufferPoolLatch.release();
    }
  }
  protected void hook484() throws DatabaseException {
    bufferPoolLatch.acquire();
    original();
  }
}
