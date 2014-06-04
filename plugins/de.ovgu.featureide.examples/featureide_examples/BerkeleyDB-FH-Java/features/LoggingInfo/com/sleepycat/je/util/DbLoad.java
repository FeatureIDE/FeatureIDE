package com.sleepycat.je.util;
public class DbLoad {
  public boolean load() throws IOException, DatabaseException {
    Tracer.trace(Level.INFO,DbInternal.envGetEnvironmentImpl(env),"DbLoad.load of " + dbName + " starting");
    return original();
  }
  protected void hook835() throws IOException, DatabaseException {
    Tracer.trace(Level.INFO,DbInternal.envGetEnvironmentImpl(env),"DbLoad.load of " + dbName + " ending.");
    original();
  }
}
