package com.sleepycat.je.dbi;
public class DatabaseImpl {
  public boolean verify(  VerifyConfig config,  DatabaseStats emptyStats) throws DatabaseException {
    if (tree == null) {
      return true;
    }
    PrintStream out=config.getShowProgressStream();
    if (out == null) {
      out=System.err;
    }
    StatsAccumulator statsAcc=new StatsAccumulator(out,config.getShowProgressInterval(),emptyStats){
      void verifyNode(      Node node){
        try {
          node.verify(null);
        }
 catch (        DatabaseException INE) {
          progressStream.println(INE);
        }
      }
    }
;
    boolean ok=walkDatabaseTree(statsAcc,out,config.getPrintInfo());
    statsAcc.copyToStats(emptyStats);
    return ok;
  }
}
