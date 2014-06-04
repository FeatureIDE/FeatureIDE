package com.sleepycat.je.tree;
import com.sleepycat.je.latch.LatchNotHeldException;
public final class TreeIterator {
  protected void hook755() throws DatabaseException {
    if (nextBin != null) {
      nextBin.releaseLatch();
    }
    original();
  }
  protected void hook756() throws DatabaseException {
    if (nextBin != null) {
      nextBin.latch();
    }
    original();
  }
  protected void hook757(){
    try {
      if (nextBin != null) {
        nextBin.releaseLatch();
      }
    }
 catch (    LatchNotHeldException e) {
    }
    original();
  }
  protected void hook758() throws DatabaseException {
    nextBin.latch();
    original();
  }
  protected void hook759(){
    try {
      if (nextBin != null) {
        nextBin.releaseLatch();
      }
    }
 catch (    LatchNotHeldException e) {
    }
    original();
  }
}
