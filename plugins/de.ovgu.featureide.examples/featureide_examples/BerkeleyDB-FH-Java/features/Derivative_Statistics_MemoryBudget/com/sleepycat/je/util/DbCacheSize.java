package com.sleepycat.je.util;
import com.sleepycat.je.EnvironmentStats;
public class DbCacheSize {
  private static void printStats(  PrintStream out,  Environment env,  String msg) throws DatabaseException {
    out.println();
    out.println(msg + ':');
    EnvironmentStats stats=env.getStats(null);
    out.println("CacheSize=" + INT_FORMAT.format(stats.getCacheTotalBytes()) + " BtreeSize="+ INT_FORMAT.format(stats.getCacheDataBytes()));
    if (stats.getNNodesScanned() > 0) {
      out.println("*** All records did not fit in the cache ***");
    }
  }
  protected static void hook831(  PrintStream out,  Environment env) throws DatabaseException {
    printStats(out,env,"Stats for internal nodes only (after preload)");
    original(out,env);
  }
  protected static void hook832(  PrintStream out,  Environment env) throws DatabaseException {
    printStats(out,env,"Stats for internal and leaf nodes (after insert)");
    original(out,env);
  }
@MethodObject static class DbCacheSize_insertRecords {
    protected void hook833() throws DatabaseException {
      stats=env.getStats(null);
      if (stats.getNNodesScanned() > 0) {
        out.println("*** Ran out of cache memory at record " + i + " -- try increasing the Java heap size ***");
        throw new ReturnVoid();
      }
      original();
    }
  }
}
