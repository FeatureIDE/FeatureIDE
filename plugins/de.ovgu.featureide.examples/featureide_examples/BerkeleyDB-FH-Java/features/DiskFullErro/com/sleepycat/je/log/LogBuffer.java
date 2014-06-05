package com.sleepycat.je.log;
class LogBuffer {
  private boolean rewriteAllowed;
  boolean getRewriteAllowed(){
    return rewriteAllowed;
  }
  void setRewriteAllowed(){
    rewriteAllowed=true;
  }
  LogBuffer(  ByteBuffer buffer,  long firstLsn) throws DatabaseException {
    rewriteAllowed=false;
  }
  void reinit() throws DatabaseException {
    original();
    rewriteAllowed=false;
  }
}
