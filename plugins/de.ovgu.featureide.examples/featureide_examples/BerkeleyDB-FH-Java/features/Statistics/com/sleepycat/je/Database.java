package com.sleepycat.je;
public class Database {
  public DatabaseStats getStats(  StatsConfig config) throws DatabaseException {
    checkEnv();
    checkRequiredDbState(OPEN,"Can't call Database.stat");
    StatsConfig useConfig=(config == null) ? StatsConfig.DEFAULT : config;
    if (databaseImpl != null) {
      this.hook38();
      return databaseImpl.stat(useConfig);
    }
    return null;
  }
  protected void hook38() throws DatabaseException {
  }
}
