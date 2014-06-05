package com.sleepycat.je.recovery;
public class Checkpointer {
@MethodObject static class Checkpointer_doCheckpoint {
    protected void hook525() throws DatabaseException {
      try {
        original();
      }
 catch (      DatabaseException e) {
        Tracer.trace(_this.envImpl,"Checkpointer","doCheckpoint","checkpointId=" + _this.checkpointId,e);
        throw e;
      }
    }
  }
}
