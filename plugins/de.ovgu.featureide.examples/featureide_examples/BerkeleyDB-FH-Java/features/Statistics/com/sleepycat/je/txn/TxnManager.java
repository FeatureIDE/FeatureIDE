package com.sleepycat.je.txn;
import com.sleepycat.je.StatsConfig;
import com.sleepycat.je.TransactionStats;
public class TxnManager {
  private int numCommits;
  private int numAborts;
  private int numXAPrepares;
  private int numXACommits;
  private int numXAAborts;
  /** 
 * Collect transaction related stats.
 */
  public TransactionStats txnStat(  StatsConfig config) throws DatabaseException {
    TransactionStats stats=new TransactionStats();
    this.hook820(config,stats);
    return stats;
  }
  /** 
 * Collect lock related stats.
 */
  public LockStats lockStat(  StatsConfig config) throws DatabaseException {
    return lockManager.lockStat(config);
  }
  protected void hook820(  StatsConfig config,  TransactionStats stats) throws DatabaseException {
    stats.setNCommits(numCommits);
    stats.setNAborts(numAborts);
    stats.setNXAPrepares(numXAPrepares);
    stats.setNXACommits(numXACommits);
    stats.setNXAAborts(numXAAborts);
    stats.setNActive(allTxns.size());
    TransactionStats.Active[] activeSet=new TransactionStats.Active[stats.getNActive()];
    stats.setActiveTxns(activeSet);
    Iterator iter=allTxns.iterator();
    int i=0;
    while (iter.hasNext()) {
      Locker txn=(Locker)iter.next();
      activeSet[i]=new TransactionStats.Active(txn.toString(),txn.getId(),0);
      i++;
    }
    if (config.getClear()) {
      numCommits=0;
      numAborts=0;
      numXACommits=0;
      numXAAborts=0;
    }
  }
  protected void hook824() throws DatabaseException {
    numCommits=0;
    numAborts=0;
    numXAPrepares=0;
    numXACommits=0;
    numXAAborts=0;
    original();
  }
  protected void hook825(  boolean isCommit) throws DatabaseException {
    if (isCommit) {
      numCommits++;
    }
 else {
      numAborts++;
    }
    original(isCommit);
  }
  protected void hook826(  boolean isPrepare) throws DatabaseException {
    if (isPrepare) {
      numXAPrepares++;
    }
    original(isPrepare);
  }
  protected void hook827(  boolean isCommit) throws DatabaseException {
    if (isCommit) {
      numXACommits++;
    }
 else {
      numXAAborts++;
    }
    original(isCommit);
  }
}
