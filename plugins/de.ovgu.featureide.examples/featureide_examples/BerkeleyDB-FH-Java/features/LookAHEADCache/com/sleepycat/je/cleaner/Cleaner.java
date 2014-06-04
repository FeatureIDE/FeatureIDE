package com.sleepycat.je.cleaner;
public class Cleaner {
  int lookAheadCacheSize;
  protected void hook94(  DbConfigManager cm) throws DatabaseException {
    lookAheadCacheSize=cm.getInt(EnvironmentParams.CLEANER_LOOK_AHEAD_CACHE_SIZE);
    original(cm);
  }
}
