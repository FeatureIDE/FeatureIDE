package com.sleepycat.je.dbi;
class PreloadLSNTreeWalker {
  protected void releaseRootIN(  IN root) throws DatabaseException {
    root.releaseLatch();
  }
  protected void hook352(  long lsn,  INEntry inEntry,  IN in) throws DatabaseException {
    in.latch();
    try {
      original(lsn,inEntry,in);
    }
  finally {
      in.releaseLatch();
    }
  }
}
