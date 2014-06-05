package com.sleepycat.je.util;
public class DbVerify {
  protected void hook851(  EnvironmentImpl envImpl) throws DatabaseException {
    Tracer.trace(Level.INFO,envImpl,"DbVerify.verify of " + dbName + " starting");
    original(envImpl);
  }
  protected void hook852(  EnvironmentImpl envImpl) throws DatabaseException {
    Tracer.trace(Level.INFO,envImpl,"DbVerify.verify of " + dbName + " ending");
    original(envImpl);
  }
}
