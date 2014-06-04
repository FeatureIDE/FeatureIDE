package com.sleepycat.je;
public class Database {
  public DatabaseStats verify(  VerifyConfig config) throws DatabaseException {
    checkEnv();
    checkRequiredDbState(OPEN,"Can't call Database.verify");
    this.hook37();
    VerifyConfig useConfig=(config == null) ? VerifyConfig.DEFAULT : config;
    DatabaseStats stats=databaseImpl.getEmptyStats();
    databaseImpl.verify(useConfig,stats);
    return stats;
  }
  protected void hook37() throws DatabaseException {
  }
}
