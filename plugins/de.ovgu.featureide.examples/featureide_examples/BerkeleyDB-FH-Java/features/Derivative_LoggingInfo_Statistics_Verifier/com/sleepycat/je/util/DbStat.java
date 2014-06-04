package com.sleepycat.je.util;
public class DbStat {
  protected void hook849() throws DatabaseException {
    Tracer.trace(Level.INFO,DbInternal.envGetEnvironmentImpl(env),"DbStat.stats of " + dbName + " ending");
    original();
  }
  protected void hook850() throws DatabaseException {
    Tracer.trace(Level.INFO,DbInternal.envGetEnvironmentImpl(env),"DbStat.stats of " + dbName + " starting");
    original();
  }
}
