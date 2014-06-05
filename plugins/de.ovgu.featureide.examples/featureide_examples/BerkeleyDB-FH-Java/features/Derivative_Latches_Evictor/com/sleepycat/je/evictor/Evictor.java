package com.sleepycat.je.evictor;
import com.sleepycat.je.latch.LatchSupport;
public class Evictor {
  protected long hook374(  INList inList,  IN target,  ScanIterator scanIter,  boolean envIsReadOnly,  long evictedBytes) throws DatabaseException {
    try {
      evictedBytes=original(inList,target,scanIter,envIsReadOnly,evictedBytes);
    }
  finally {
      target.releaseLatchIfOwner();
    }
    return evictedBytes;
  }
  protected long hook375(  IN child,  IN parent,  int index,  INList inlist,  ScanIterator scanIter,  boolean envIsReadOnly,  long evictBytes) throws DatabaseException {
    try {
      evictBytes=original(child,parent,index,inlist,scanIter,envIsReadOnly,evictBytes);
    }
  finally {
      parent.releaseLatch();
    }
    return evictBytes;
  }
  protected void hook378(  IN parent) throws DatabaseException {
    assert parent.isLatchOwner();
    original(parent);
  }
  protected long hook379(  IN parent,  int index,  INList inlist,  ScanIterator scanIter,  boolean envIsReadOnly,  long evictBytes,  IN renewedChild) throws DatabaseException {
    try {
      evictBytes=original(parent,index,inlist,scanIter,envIsReadOnly,evictBytes,renewedChild);
    }
  finally {
      renewedChild.releaseLatch();
    }
    return evictBytes;
  }
@MethodObject static class Evictor_evictBatch {
    long execute() throws DatabaseException {
      long result=original();
      assert LatchSupport.countLatchesHeld() == 0 : "latches held = " + LatchSupport.countLatchesHeld();
      return result;
    }
    protected void hook376() throws DatabaseException {
      inList.latchMajor();
      original();
    }
    protected void hook377() throws DatabaseException {
      inList.releaseMajorLatch();
      original();
    }
  }
}
