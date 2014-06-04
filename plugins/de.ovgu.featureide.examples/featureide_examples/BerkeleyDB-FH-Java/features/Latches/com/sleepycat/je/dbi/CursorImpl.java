package com.sleepycat.je.dbi;
import com.sleepycat.je.latch.LatchNotHeldException;
import com.sleepycat.je.latch.LatchSupport;
public class CursorImpl {
  public void releaseBIN() throws LatchNotHeldException {
    if (bin != null) {
      bin.releaseLatchIfOwner();
    }
  }
  public void latchBINs() throws DatabaseException {
    latchBIN();
    latchDBIN();
  }
  public void releaseBINs() throws LatchNotHeldException {
    releaseBIN();
    releaseDBIN();
  }
  public void releaseDBIN() throws LatchNotHeldException {
    if (dupBin != null) {
      dupBin.releaseLatchIfOwner();
    }
  }
  private boolean checkAlreadyLatched(  boolean alreadyLatched){
    if (alreadyLatched) {
      if (dupBin != null) {
        return dupBin.isLatchOwner();
      }
 else       if (bin != null) {
        return bin.isLatchOwner();
      }
    }
    return true;
  }
  protected void hook206() throws DatabaseException, CloneNotSupportedException {
    latchBINs();
    original();
  }
  protected void hook207() throws DatabaseException {
    releaseBINs();
    original();
  }
  protected void hook208(  BIN bin){
    assert bin.isLatchOwner();
    original(bin);
  }
  protected void hook209(  BIN abin) throws DatabaseException {
    abin.releaseLatch();
    original(abin);
  }
  protected void hook210(  DBIN abin) throws DatabaseException {
    abin.releaseLatch();
    original(abin);
  }
  protected void hook211() throws DatabaseException {
    dupBin.releaseLatch();
    original();
  }
  protected void hook212(  LockType lockType) throws DatabaseException {
    latchBIN();
    try {
      original(lockType);
    }
  finally {
      releaseBIN();
    }
  }
  protected void hook213(  boolean isDup,  LN ln,  LockResult lockResult,  LockResult dclLockResult,  DIN dupRoot) throws DatabaseException {
    try {
      original(isDup,ln,lockResult,dclLockResult,dupRoot);
    }
  finally {
      if (dupRoot != null) {
        dupRoot.releaseLatchIfOwner();
      }
    }
  }
  protected void hook214() throws DatabaseException {
    releaseBINs();
    original();
  }
  protected void hook215() throws DatabaseException {
    releaseBINs();
    original();
  }
  protected void hook216() throws DatabaseException {
    releaseBINs();
    original();
  }
  protected void hook217() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook218(  DatabaseEntry data,  DatabaseEntry foundKey,  DatabaseEntry foundData,  boolean isDup) throws DatabaseException {
    try {
      original(data,foundKey,foundData,isDup);
    }
  finally {
      releaseBINs();
    }
  }
  protected void hook219() throws DatabaseException {
    latchBINs();
    original();
  }
  protected void hook220() throws DatabaseException {
    if (dupBin == null) {
      latchBIN();
    }
 else {
      latchDBIN();
    }
    original();
  }
  protected void hook221(  DatabaseEntry foundKey,  DatabaseEntry foundData,  LockType lockType,  boolean first) throws DatabaseException {
    assert checkAlreadyLatched(true) : dumpToString(true);
    try {
      original(foundKey,foundData,lockType,first);
    }
  finally {
      releaseBINs();
    }
  }
  protected void hook222() throws DatabaseException {
    latchBIN();
    original();
  }
  protected void hook223(  LockType lockType) throws DatabaseException {
    try {
      original(lockType);
    }
  finally {
      releaseBINs();
    }
  }
  protected void hook224(  boolean alreadyLatched) throws DatabaseException {
    assert checkAlreadyLatched(alreadyLatched) : dumpToString(true);
    original(alreadyLatched);
  }
  protected boolean hook225(  boolean alreadyLatched) throws DatabaseException {
    assert checkAlreadyLatched(alreadyLatched) : dumpToString(true);
    if (!alreadyLatched) {
      latchBIN();
    }
 else {
      alreadyLatched=false;
    }
    return original(alreadyLatched);
  }
  protected boolean hook226(  boolean alreadyLatched) throws DatabaseException {
    alreadyLatched=false;
    return original(alreadyLatched);
  }
  protected void hook227() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook228() throws DatabaseException {
    latchBIN();
    original();
  }
  protected void hook229() throws DatabaseException {
    releaseBIN();
    original();
  }
  protected void hook230(  boolean alreadyLatched) throws DatabaseException {
    alreadyLatched=true;
    original(alreadyLatched);
  }
  protected void hook231() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0 : LatchSupport.latchesHeldToString();
    original();
  }
  private void flushBINToBeRemoved() throws DatabaseException {
    binToBeRemoved.latch();
    original();
  }
  protected void hook232() throws DatabaseException {
    binToBeRemoved.releaseLatch();
    original();
  }
  private void flushDBINToBeRemoved() throws DatabaseException {
    dupBinToBeRemoved.latch();
    original();
  }
  protected void hook233() throws DatabaseException {
    dupBinToBeRemoved.releaseLatch();
    original();
  }
  protected void hook234(  boolean first,  DIN duplicateRoot,  IN in,  boolean found) throws DatabaseException {
    try {
      original(first,duplicateRoot,in,found);
    }
 catch (    DatabaseException e) {
      if (in != null) {
        in.releaseLatch();
      }
      throw e;
    }
  }
  protected void hook235(  DatabaseEntry matchKey,  DatabaseEntry matchData,  SearchMode searchMode,  LockType lockType,  boolean foundSomething,  boolean foundExactKey,  boolean foundExactData,  boolean foundLast,  boolean exactSearch,  BINBoundary binBoundary) throws DatabaseException {
    try {
      original(matchKey,matchData,searchMode,lockType,foundSomething,foundExactKey,foundExactData,foundLast,exactSearch,binBoundary);
    }
 catch (    DatabaseException e) {
      releaseBIN();
      throw e;
    }
  }
  protected void hook236(  DIN duplicateRoot) throws DatabaseException {
    duplicateRoot.latch();
    releaseBIN();
    original(duplicateRoot);
  }
  protected void hook237() throws DatabaseException {
    latchBINs();
    original();
  }
  protected void hook238() throws DatabaseException {
    releaseBINs();
    original();
  }
  protected void hook239(  DIN dupRoot) throws DatabaseException {
    dupRoot.latch();
    latchDBIN();
    original(dupRoot);
  }
  protected void hook240() throws DatabaseException {
    latchBIN();
    original();
  }
  protected void hook241(  DIN dupRoot) throws DatabaseException {
    dupRoot.releaseLatch();
    releaseBINs();
    original(dupRoot);
  }
  protected void hook242(  boolean isDBINLatched,  DIN dupRoot) throws DatabaseException {
    if (isDBINLatched) {
      if (!dupRoot.latchNoWait()) {
        releaseDBIN();
        dupRoot.latch();
        latchDBIN();
      }
    }
 else {
      dupRoot.latch();
    }
    original(isDBINLatched,dupRoot);
  }
  protected void hook243() throws DatabaseException {
    assert bin.isLatchOwner();
    original();
  }
  protected void hook264(  DIN dupRoot) throws DatabaseException {
    dupRoot.releaseLatch();
    original(dupRoot);
  }
  protected void hook265(  DIN dupRoot) throws DatabaseException {
    dupRoot.latch();
    releaseBIN();
    original(dupRoot);
  }
  protected void hook266() throws DatabaseException {
    releaseBINs();
    original();
  }
  protected void hook267() throws DatabaseException {
    releaseBIN();
    original();
  }
  protected void hook268(  DIN dupRoot) throws DatabaseException {
    dupRoot.releaseLatch();
    original(dupRoot);
  }
  protected void hook269() throws DatabaseException {
    releaseBINs();
    original();
  }
  protected void hook270() throws DatabaseException {
    releaseBINs();
    original();
  }
  protected void hook271() throws DatabaseException {
    releaseBINs();
    original();
  }
  protected void hook272() throws DatabaseException {
    assert checkAlreadyLatched(true) : dumpToString(true);
    original();
  }
  protected void hook273() throws DatabaseException {
    releaseBIN();
    original();
  }
  protected void hook274(  IN in,  DIN dupRoot) throws DatabaseException {
    dupRoot.latch();
    in.releaseLatch();
    original(in,dupRoot);
  }
@MethodObject static class CursorImpl_latchBIN {
    protected void hook244() throws DatabaseException {
      while (_this.bin != null) {
        original();
      }
      throw new ReturnObject(null);
    }
    protected void hook245() throws DatabaseException {
      waitingOn=_this.bin;
      waitingOn.latch();
      if (_this.bin == waitingOn) {
        original();
      }
      waitingOn.releaseLatch();
    }
  }
@MethodObject static class CursorImpl_getNextDuplicate {
    protected void hook250() throws DatabaseException {
      assert _this.checkAlreadyLatched(alreadyLatched) : _this.dumpToString(true);
      original();
    }
    protected void hook251() throws DatabaseException {
      if (!alreadyLatched) {
        _this.latchDBIN();
      }
 else {
        alreadyLatched=false;
      }
      original();
    }
    protected void hook252() throws DatabaseException {
      _this.releaseDBIN();
      original();
    }
    protected void hook253() throws DatabaseException {
      assert LatchSupport.countLatchesHeld() == 0;
      original();
    }
    protected void hook254() throws DatabaseException {
      assert (LatchSupport.countLatchesHeld() == 0);
      _this.dupBinToBeRemoved.latch();
      original();
    }
    protected void hook255() throws DatabaseException {
      _this.dupBinToBeRemoved.releaseLatch();
      original();
    }
    protected void hook256() throws DatabaseException {
      alreadyLatched=true;
      original();
    }
    protected void hook257() throws DatabaseException {
      assert LatchSupport.countLatchesHeld() == 0;
      original();
    }
  }
@MethodObject static class CursorImpl_lockNextKeyForInsert {
    protected void hook248() throws DatabaseException {
      latched=true;
      try {
        original();
      }
  finally {
        if (latched) {
          _this.releaseBINs();
        }
      }
    }
    protected void hook249() throws DatabaseException {
      latched=false;
      original();
    }
  }
@MethodObject static class CursorImpl_latchDBIN {
    protected void hook246() throws DatabaseException {
      while (_this.dupBin != null) {
        original();
      }
      throw new ReturnObject(null);
    }
    protected void hook247() throws DatabaseException {
      waitingOn=_this.dupBin;
      waitingOn.latch();
      if (_this.dupBin == waitingOn) {
        original();
      }
      waitingOn.releaseLatch();
    }
  }
@MethodObject static class CursorImpl_fetchCurrent {
    protected void hook258() throws DatabaseException {
      try {
        original();
      }
  finally {
        _this.releaseBINs();
      }
    }
    protected void hook259() throws DatabaseException {
      assert _this.targetBin.isLatchOwner();
      original();
    }
    protected void hook260() throws DatabaseException {
      try {
        original();
      }
 catch (      DatabaseException DE) {
        _this.targetBin.releaseLatchIfOwner();
        throw DE;
      }
    }
    protected void hook261() throws DatabaseException {
      _this.targetBin.releaseLatchIfOwner();
      original();
    }
    protected void hook262() throws DatabaseException {
      duplicateRoot.latch();
      _this.targetBin.releaseLatch();
      original();
    }
    protected void hook263() throws DatabaseException {
      try {
        original();
      }
 catch (      DatabaseException DE) {
        _this.releaseBINs();
        throw DE;
      }
    }
  }
}
