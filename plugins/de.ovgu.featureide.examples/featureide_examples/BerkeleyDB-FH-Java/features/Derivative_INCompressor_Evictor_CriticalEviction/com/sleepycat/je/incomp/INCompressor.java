package com.sleepycat.je.incomp;
public class INCompressor {
  protected void hook391() throws DatabaseException {
    env.getEvictor().doCriticalEviction();
    original();
  }
}
