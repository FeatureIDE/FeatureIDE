package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  protected void hook318() throws DatabaseException {
    Tracer.trace(Level.FINE,this,"Env " + envHome + " daemons shutdown");
    original();
  }
  protected void hook319() throws DatabaseException {
    Tracer.trace(Level.FINE,this,"Close of environment " + envHome + " started");
    original();
  }
}
