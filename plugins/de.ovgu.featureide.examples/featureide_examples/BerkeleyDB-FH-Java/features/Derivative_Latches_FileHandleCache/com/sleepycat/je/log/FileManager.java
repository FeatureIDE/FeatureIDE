package com.sleepycat.je.log;
public class FileManager {
  private Latch fileCacheLatch;
  protected void hook449(  EnvironmentImpl envImpl) throws DatabaseException {
    fileCacheLatch=LatchSupport.makeLatch(DEBUG_NAME + "_fileCache",envImpl);
    original(envImpl);
  }
  protected FileHandle hook450(  long fileNum,  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
    fileCacheLatch.acquire();
    try {
      fileHandle=original(fileNum,fileId,fileHandle);
    }
  finally {
      fileCacheLatch.release();
    }
    return fileHandle;
  }
  /** 
 * Close all file handles and empty the cache.
 */
  public void clear() throws IOException, DatabaseException {
    fileCacheLatch.acquire();
    original();
  }
  protected void hook451() throws IOException, DatabaseException {
    try {
      original();
    }
  finally {
      fileCacheLatch.release();
    }
  }
  /** 
 * Clear a file out of the file cache regardless of mode type.
 */
  private void clearFileCache(  long fileNum) throws IOException, DatabaseException {
    fileCacheLatch.acquire();
    try {
      original(fileNum);
    }
  finally {
      fileCacheLatch.release();
    }
  }
}
