package com.sleepycat.je.recovery;
public class Checkpointer {
@MethodObject static class Checkpointer_doCheckpoint {
    protected void hook547() throws DatabaseException {
synchronized (_this.envImpl.getEvictor()) {
        original();
      }
    }
  }
}
