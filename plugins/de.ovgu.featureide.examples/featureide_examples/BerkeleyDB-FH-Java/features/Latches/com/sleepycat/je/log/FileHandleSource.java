package com.sleepycat.je.log;
class FileHandleSource {
  /** 
 * @see LogSource#release
 */
  public void release() throws DatabaseException {
    fileHandle.release();
  }
}
