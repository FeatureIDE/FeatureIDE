package com.sleepycat.je.log;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
class FileHandle {
  private Latch fileLatch;
  void latch() throws DatabaseException {
    fileLatch.acquire();
  }
  boolean latchNoWait() throws DatabaseException {
    return fileLatch.acquireNoWait();
  }
  void release() throws DatabaseException {
    fileLatch.release();
  }
  protected void hook444(  String fileName,  EnvironmentImpl env){
    fileLatch=LatchSupport.makeLatch(fileName + "_fileHandle",env);
    original(fileName,env);
  }
}
