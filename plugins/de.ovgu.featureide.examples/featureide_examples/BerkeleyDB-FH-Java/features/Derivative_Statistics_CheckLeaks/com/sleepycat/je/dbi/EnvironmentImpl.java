package com.sleepycat.je.dbi;
public class EnvironmentImpl {
@MethodObject static class EnvironmentImpl_checkLeaks {
    protected void hook313() throws DatabaseException {
      statsConfig=new StatsConfig();
      statsConfig.setFast(false);
      lockStat=_this.lockStat(statsConfig);
      if (lockStat.getNTotalLocks() != 0) {
        clean=false;
        System.out.println("Problem: " + lockStat.getNTotalLocks() + " locks left");
        _this.txnManager.getLockManager().dump();
      }
      txnStat=_this.txnStat(statsConfig);
      if (txnStat.getNActive() != 0) {
        clean=false;
        System.out.println("Problem: " + txnStat.getNActive() + " txns left");
        active=txnStat.getActiveTxns();
        if (active != null) {
          for (int i=0; i < active.length; i+=1) {
            System.out.println(active[i]);
          }
        }
      }
      original();
    }
  }
}
