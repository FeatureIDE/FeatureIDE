package com.sleepycat.je;
public class Environment {
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public EnvironmentStats getStats(  StatsConfig config) throws DatabaseException {
    StatsConfig useConfig=(config == null) ? StatsConfig.DEFAULT : config;
    if (environmentImpl != null) {
      return environmentImpl.loadStats(useConfig);
    }
 else {
      return new EnvironmentStats();
    }
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public LockStats getLockStats(  StatsConfig config) throws DatabaseException {
    checkHandleIsValid();
    checkEnv();
    StatsConfig useConfig=(config == null) ? StatsConfig.DEFAULT : config;
    return environmentImpl.lockStat(useConfig);
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public TransactionStats getTransactionStats(  StatsConfig config) throws DatabaseException {
    checkHandleIsValid();
    checkEnv();
    StatsConfig useConfig=(config == null) ? StatsConfig.DEFAULT : config;
    return environmentImpl.txnStat(useConfig);
  }
}
