package com.sleepycat.je.incomp;
public class INCompressor {
  protected void hook392(  int binQueueSize) throws DatabaseException {
    Tracer.trace(Level.FINE,env,"InCompress.doCompress called, queue size: " + binQueueSize);
    original(binQueueSize);
  }
}
