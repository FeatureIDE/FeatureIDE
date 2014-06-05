package com.sleepycat.je.recovery;
public class Checkpointer {
  protected void hook526(  CheckpointReference targetRef,  Map dirtyMap,  int currentLevel,  boolean logProvisionally,  boolean allowDeltas,  long checkpointStart,  Tree tree,  SearchResult result,  boolean mustLogParent) throws DatabaseException {
    try {
      original(targetRef,dirtyMap,currentLevel,logProvisionally,allowDeltas,checkpointStart,tree,result,mustLogParent);
    }
  finally {
      result.parent.releaseLatch();
    }
  }
  protected void hook527(  IN target,  IN parent,  boolean allowDeltas,  long checkpointStart,  boolean logProvisionally,  long newLsn,  boolean mustLogParent) throws DatabaseException {
    try {
      original(target,parent,allowDeltas,checkpointStart,logProvisionally,newLsn,mustLogParent);
    }
  finally {
      target.releaseLatch();
    }
  }
@MethodObject static class Checkpointer_selectDirtyINs {
    protected void hook528() throws DatabaseException {
      try {
        original();
      }
  finally {
        inMemINs.releaseMajorLatchIfHeld();
      }
    }
    protected void hook529() throws DatabaseException {
      inMemINs.latchMajor();
      original();
    }
    protected void hook530() throws DatabaseException {
      try {
        original();
      }
  finally {
        in.releaseLatch();
      }
    }
  }
}
