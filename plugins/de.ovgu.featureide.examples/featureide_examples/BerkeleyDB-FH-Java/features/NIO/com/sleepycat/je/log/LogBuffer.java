package com.sleepycat.je.log;
class LogBuffer {
  protected void hook481(  int capacity) throws DatabaseException {
    buffer=ByteBuffer.allocateDirect(capacity);
    original(capacity);
  }
}
