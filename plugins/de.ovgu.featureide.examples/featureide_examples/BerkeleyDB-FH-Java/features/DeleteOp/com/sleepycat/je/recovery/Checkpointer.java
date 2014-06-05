package com.sleepycat.je.recovery;
public class Checkpointer {
  protected void hook546(  SortedMap dirtyMap,  boolean allowDeltas,  long checkpointStart,  Integer currentLevel,  boolean logProvisionally,  CheckpointReference targetRef) throws DatabaseException {
    if (!(targetRef.db.isDeleted())) {
      flushIN(targetRef,dirtyMap,currentLevel.intValue(),logProvisionally,allowDeltas,checkpointStart);
    }
    original(dirtyMap,allowDeltas,checkpointStart,currentLevel,logProvisionally,targetRef);
  }
}
