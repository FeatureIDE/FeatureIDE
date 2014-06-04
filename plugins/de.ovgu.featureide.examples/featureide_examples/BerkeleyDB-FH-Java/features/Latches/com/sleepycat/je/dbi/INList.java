package com.sleepycat.je.dbi;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
public class INList {
  private Set addedINs=null;
  private Latch majorLatch;
  private Latch minorLatch;
  /** 
 * The locking hierarchy is:
 * 1. INList major latch.
 * 2. IN latch.
 * In other words, the INList major latch must be taken before any IN
 * latches to avoid deadlock. 
 */
  public void latchMajor() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    majorLatch.acquire();
  }
  public void releaseMajorLatchIfHeld() throws DatabaseException {
    if (majorLatch.isOwner()) {
      releaseMajorLatch();
    }
  }
  public void releaseMajorLatch() throws DatabaseException {
    latchMinorAndDumpAddedINs();
    majorLatch.release();
  }
  private void dumpAddedINsIntoMajorSet(){
    if (addedINs.size() > 0) {
      ins.addAll(addedINs);
      addedINs.clear();
    }
  }
  void latchMinorAndDumpAddedINs() throws DatabaseException {
    latchMinor();
    try {
      dumpAddedINsIntoMajorSet();
    }
  finally {
      releaseMinorLatch();
    }
  }
  private void latchMinor() throws DatabaseException {
    minorLatch.acquire();
  }
  private void releaseMinorLatch() throws DatabaseException {
    minorLatch.release();
  }
  protected void hook338(  EnvironmentImpl envImpl){
    addedINs=new HashSet();
    majorLatch=LatchSupport.makeLatch(DEBUG_NAME + " Major Latch",envImpl);
    minorLatch=LatchSupport.makeLatch(DEBUG_NAME + " Minor Latch",envImpl);
    original(envImpl);
  }
  protected void hook339(  EnvironmentImpl envImpl) throws DatabaseException {
    majorLatch=LatchSupport.makeLatch(DEBUG_NAME + " Major Latch",envImpl);
    minorLatch=LatchSupport.makeLatch(DEBUG_NAME + " Minor Latch",envImpl);
    original(envImpl);
  }
  protected void hook340() throws DatabaseException {
    addedINs=new HashSet();
    original();
  }
  /** 
 * An IN is getting evicted or is displaced by recovery.  Caller is
 * responsible for acquiring the major latch before calling this and
 * releasing it when they're done.
 */
  public void removeLatchAlreadyHeld(  IN in) throws DatabaseException {
    assert majorLatch.isOwner();
    original(in);
  }
  protected boolean hook341(  IN in,  boolean removeDone) throws DatabaseException {
    if (!removeDone) {
      minorLatch.acquire();
      try {
        removeDone=addedINs.remove(in);
        dumpAddedINsIntoMajorSet();
      }
  finally {
        minorLatch.release();
      }
    }
    return original(in,removeDone);
  }
  /** 
 * An IN is getting swept or is displaced by recovery.
 */
  public void remove(  IN in) throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    majorLatch.acquire();
    try {
      original(in);
    }
  finally {
      releaseMajorLatch();
    }
  }
  public SortedSet tailSet(  IN in) throws DatabaseException {
    assert majorLatch.isOwner();
    return original(in);
  }
  public IN first() throws DatabaseException {
    assert majorLatch.isOwner();
    return original();
  }
  /** 
 * Return an iterator over the main 'ins' set.  Returned iterator will not
 * show the elements in addedINs.
 * The major latch should be held before entering.  The caller is
 * responsible for releasing the major latch when they're finished with the
 * iterator.
 * @return an iterator over the main 'ins' set.
 */
  public Iterator iterator(){
    assert majorLatch.isOwner();
    return original();
  }
  /** 
 * Clear the entire list during recovery and at shutdown.
 */
  public void clear() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    majorLatch.acquire();
    minorLatch.acquire();
    original();
  }
  protected void hook342() throws DatabaseException {
    addedINs.clear();
    minorLatch.release();
    releaseMajorLatch();
    original();
  }
@MethodObject static class INList_add {
    protected void hook343() throws DatabaseException {
      try {
        original();
      }
  finally {
        if (addToMajor) {
          _this.releaseMajorLatchIfHeld();
        }
      }
    }
    protected void hook344() throws DatabaseException {
      enteredWithLatchHeld=_this.majorLatch.isOwner();
      original();
    }
    protected void hook345() throws DatabaseException {
      if (enteredWithLatchHeld) {
        addToMajor=false;
      }
 else {
        if (!(_this.majorLatch.acquireNoWait())) {
          addToMajor=false;
        }
      }
      if (addToMajor) {
        original();
      }
 else {
        _this.minorLatch.acquire();
        try {
          _this.addAndSetMemory(_this.addedINs,in);
        }
  finally {
          _this.minorLatch.release();
        }
        if (!enteredWithLatchHeld) {
          if (_this.majorLatch.acquireNoWait()) {
            try {
              _this.latchMinorAndDumpAddedINs();
            }
  finally {
              _this.releaseMajorLatch();
            }
          }
        }
      }
    }
  }
}
