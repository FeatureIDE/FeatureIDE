package com.sleepycat.je.log;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
class LogBuffer {
  private Latch readLatch;
  /** 
 * When modifying the buffer, acquire the readLatch. Call release() to
 * release the latch. Note that containsLsn() acquires the latch for
 * reading.
 */
  public void latchForWrite() throws DatabaseException {
    readLatch.acquire();
  }
  /** 
 * @see LogSource#release
 */
  public void release() throws DatabaseException {
    readLatch.releaseIfOwner();
  }
  protected void hook479(  EnvironmentImpl env) throws DatabaseException {
    readLatch=LatchSupport.makeLatch(DEBUG_NAME,env);
    original(env);
  }
  void reinit() throws DatabaseException {
    readLatch.acquire();
    original();
    readLatch.release();
  }
  /** 
 * This LSN has been written to the log.
 */
  void registerLsn(  long lsn) throws DatabaseException {
    readLatch.acquire();
    try {
      original(lsn);
    }
  finally {
      readLatch.release();
    }
  }
  /** 
 * Support for reading a log entry out of a still-in-memory log
 * @return true if this buffer holds the entry at this LSN. The buffer will
 * be latched for read. Returns false if LSN is not here, and
 * releases the read latch.
 */
  boolean containsLsn(  long lsn) throws DatabaseException {
    readLatch.acquire();
    return original(lsn);
  }
  protected void hook480() throws DatabaseException {
    readLatch.release();
    original();
  }
}
