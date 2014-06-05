package com.sleepycat.je.evictor;
public class Evictor {
@MethodObject static class Evictor_evictBatch {
    protected void hook368() throws DatabaseException {
      msg+=" nNodesSelected=" + _this.nNodesSelectedThisRun + " nEvicted="+ _this.nNodesEvictedThisRun+ " nBINsStripped="+ _this.nBINsStrippedThisRun;
      original();
    }
    protected void hook369() throws DatabaseException {
      msg+="pass=" + _this.nEvictPasses;
      original();
    }
  }
}
