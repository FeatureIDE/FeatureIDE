package com.sleepycat.je;
import com.sleepycat.je.latch.LatchSupport;
public class Cursor {
  protected void hook19(  CursorImpl dup) throws DatabaseException {
    dup.latchBINs();
    original(dup);
  }
  protected void hook20(  CursorImpl origCursor,  CursorImpl dup) throws DatabaseException {
    if (origCursor != null) {
      origCursor.releaseBINs();
    }
    if (dup != null) {
      dup.releaseBINs();
    }
    original(origCursor,dup);
  }
  protected void hook21(  CursorImpl origCursor) throws DatabaseException {
    if (origCursor != null) {
      origCursor.releaseBINs();
    }
    original(origCursor);
  }
  protected void hook22() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0 : LatchSupport.latchesHeldToString();
    original();
  }
  protected void hook23() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 1 : LatchSupport.latchesHeldToString();
    original();
  }
  protected void hook24() throws DatabaseException {
    cursorImpl.releaseBINs();
    original();
  }
  protected void hook25(  CursorImpl dup,  DatabaseEntry key,  DatabaseEntry data,  LockType searchLockType,  LockType advanceLockType,  SearchMode searchMode,  boolean advanceAfterRangeSearch,  OperationStatus status,  boolean keyChange) throws DatabaseException {
    try {
      original(dup,key,data,searchLockType,advanceLockType,searchMode,advanceAfterRangeSearch,status,keyChange);
    }
  finally {
      cursorImpl.releaseBINs();
      if (status != OperationStatus.SUCCESS && dup != cursorImpl) {
        dup.releaseBINs();
      }
    }
  }
  protected void hook26() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook27() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook28() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook29() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook30() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook31() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook32(  CursorImpl origCursor) throws DatabaseException {
    origCursor.releaseBINs();
    original(origCursor);
  }
  protected void hook33(  CursorImpl origCursor) throws DatabaseException {
    origCursor.latchBINs();
    original(origCursor);
  }
  protected void hook34(  CursorImpl origCursor) throws DatabaseException {
    origCursor.releaseBINs();
    original(origCursor);
  }
  protected void hook35(  CursorImpl origCursor) throws DatabaseException {
    origCursor.latchBINs();
    original(origCursor);
  }
}
