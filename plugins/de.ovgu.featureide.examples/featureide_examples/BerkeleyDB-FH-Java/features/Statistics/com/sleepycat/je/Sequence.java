package com.sleepycat.je;
public class Sequence {
  private int nGets;
  private int nCachedGets;
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public SequenceStats getStats(  StatsConfig config) throws DatabaseException {
    if (config == null) {
      config=StatsConfig.DEFAULT;
    }
    if (!config.getFast()) {
      Cursor cursor=db.openCursor(null,null);
      try {
        readDataRequired(cursor,LockMode.READ_UNCOMMITTED);
      }
  finally {
        cursor.close();
      }
    }
    SequenceStats stats=new SequenceStats(nGets,nCachedGets,storedValue,cacheValue,cacheLast,rangeMin,rangeMax,cacheSize);
    if (config.getClear()) {
      nGets=0;
      nCachedGets=0;
    }
    return stats;
  }
  protected void hook83(  boolean cached) throws DatabaseException {
    nGets+=1;
    if (cached) {
      nCachedGets+=1;
    }
    original(cached);
  }
}
