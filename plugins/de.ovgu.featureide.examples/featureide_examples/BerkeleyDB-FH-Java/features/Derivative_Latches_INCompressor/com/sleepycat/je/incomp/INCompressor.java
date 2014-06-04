package com.sleepycat.je.incomp;
import com.sleepycat.je.latch.LatchSupport;
public class INCompressor {
  protected void hook393() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook394(  BIN foundBin) throws DatabaseException {
    foundBin.releaseLatch();
    original(foundBin);
  }
  protected void hook395() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 0;
    original();
  }
  protected void hook396(  BIN bin,  BINReference binRef,  boolean empty,  boolean requeued,  byte[] dupKey,  boolean isDBIN) throws DatabaseException {
    try {
      original(bin,binRef,empty,requeued,dupKey,isDBIN);
    }
  finally {
      bin.releaseLatch();
    }
  }
  protected void hook397(  byte[] mainKey,  byte[] dupKey,  Tree tree,  DIN duplicateRoot,  DBIN duplicateBin,  BIN bin) throws DatabaseException {
    try {
      original(mainKey,dupKey,tree,duplicateRoot,duplicateBin,bin);
    }
 catch (    DatabaseException DBE) {
      if (bin != null) {
        bin.releaseLatchIfOwner();
      }
      if (duplicateRoot != null) {
        duplicateRoot.releaseLatchIfOwner();
      }
      if (duplicateBin != null) {
        duplicateBin.releaseLatchIfOwner();
      }
      throw DBE;
    }
  }
  protected void hook398(  IN in) throws DatabaseException {
    assert in.isLatchOwner();
    original(in);
  }
  protected void hook399(  BINSearch binSearch) throws DatabaseException {
    if (binSearch.bin != null) {
      binSearch.bin.releaseLatch();
    }
    original(binSearch);
  }
  protected void hook400(  BIN bin) throws DatabaseException {
    bin.releaseLatch();
    original(bin);
  }
  protected void hook401(  DIN duplicateRoot,  BIN bin) throws DatabaseException {
    duplicateRoot.latch();
    bin.releaseLatch();
    original(duplicateRoot,bin);
  }
  protected void hook402(  BIN bin) throws DatabaseException {
    bin.releaseLatch();
    original(bin);
  }
}
