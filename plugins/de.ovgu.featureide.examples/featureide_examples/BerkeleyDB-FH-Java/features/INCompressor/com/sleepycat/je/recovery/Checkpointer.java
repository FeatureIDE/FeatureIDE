package com.sleepycat.je.recovery;
public class Checkpointer {
  protected void hook527(  IN target,  IN parent,  boolean allowDeltas,  long checkpointStart,  boolean logProvisionally,  long newLsn,  boolean mustLogParent) throws DatabaseException {
    envImpl.lazyCompress(target);
    original(target,parent,allowDeltas,checkpointStart,logProvisionally,newLsn,mustLogParent);
  }
}
