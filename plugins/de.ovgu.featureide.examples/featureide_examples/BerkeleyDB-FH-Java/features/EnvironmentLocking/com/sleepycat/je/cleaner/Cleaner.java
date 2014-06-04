package com.sleepycat.je.cleaner;
public class Cleaner {
  protected void hook87(  Set safeFiles) throws DatabaseException {
  }
  protected void hook115(  Set safeFiles) throws DatabaseException {
    if (!env.getFileManager().lockEnvironment(false,true)) {
      this.hook87(safeFiles);
      throw new ReturnVoid();
    }
    try {
      original(safeFiles);
    }
  finally {
      env.getFileManager().releaseExclusiveLock();
    }
  }
}
