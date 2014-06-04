package com.sleepycat.je.recovery;
public class Checkpointer {
  protected void hook520() throws DatabaseException {
    envImpl.getEvictor().doCriticalEviction();
    original();
  }
}
