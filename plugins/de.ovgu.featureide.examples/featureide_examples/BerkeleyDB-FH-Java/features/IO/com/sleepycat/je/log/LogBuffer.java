package com.sleepycat.je.log;
class LogBuffer {
  protected void hook482(  int capacity) throws DatabaseException {
    buffer=ByteBuffer.allocate(capacity);
    original(capacity);
  }
}
