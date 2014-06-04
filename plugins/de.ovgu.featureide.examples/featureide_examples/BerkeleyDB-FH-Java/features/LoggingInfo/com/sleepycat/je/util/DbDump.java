package com.sleepycat.je.util;
public class DbDump {
  public void dump() throws IOException, DatabaseException {
    original();
    Tracer.trace(Level.INFO,DbInternal.envGetEnvironmentImpl(env),"DbDump.dump of " + dbName + " ending");
  }
  protected void hook834() throws IOException, DatabaseException {
    Tracer.trace(Level.INFO,DbInternal.envGetEnvironmentImpl(env),"DbDump.dump of " + dbName + " starting");
    original();
  }
}
