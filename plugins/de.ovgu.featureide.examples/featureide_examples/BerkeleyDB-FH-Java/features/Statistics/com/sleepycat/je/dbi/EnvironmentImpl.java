package com.sleepycat.je.dbi;
import com.sleepycat.je.EnvironmentStats;
import com.sleepycat.je.StatsConfig;
import com.sleepycat.je.TransactionStats;
public class EnvironmentImpl {
  /** 
 * Retrieve and return stat information.
 */
  synchronized public EnvironmentStats loadStats(  StatsConfig config) throws DatabaseException {
    EnvironmentStats stats=new EnvironmentStats();
    this.hook314(config,stats);
    this.hook315(config,stats);
    checkpointer.loadStats(config,stats);
    cleaner.loadStats(config,stats);
    logManager.loadStats(config,stats);
    this.hook316(config,stats);
    return stats;
  }
  /** 
 * Retrieve lock statistics
 */
  synchronized public LockStats lockStat(  StatsConfig config) throws DatabaseException {
    return txnManager.lockStat(config);
  }
  /** 
 * Retrieve txn statistics
 */
  synchronized public TransactionStats txnStat(  StatsConfig config) throws DatabaseException {
    return txnManager.txnStat(config);
  }
  protected void hook314(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
  }
  protected void hook315(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
  }
  protected void hook316(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
  }
}
