package com.sleepycat.je.log;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
abstract public class LogManager {
  protected Latch logWriteLatch;
  protected void hook502(  EnvironmentImpl envImpl) throws DatabaseException {
    logWriteLatch=LatchSupport.makeLatch(DEBUG_NAME,envImpl);
    original(envImpl);
  }
  protected boolean hook503(  ByteBuffer marshalledBuffer,  int entrySize,  long currentLsn,  boolean usedTemporaryBuffer,  LogBuffer useLogBuffer) throws IOException, DatabaseException, Exception {
    useLogBuffer.latchForWrite();
    try {
      usedTemporaryBuffer=original(marshalledBuffer,entrySize,currentLsn,usedTemporaryBuffer,useLogBuffer);
    }
  finally {
      useLogBuffer.release();
    }
    return usedTemporaryBuffer;
  }
}
