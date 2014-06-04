package com.sleepycat.je.evictor;
public class Evictor {
  private Level detailedTraceLevel;
  protected void hook373(  EnvironmentImpl envImpl) throws DatabaseException {
    detailedTraceLevel=Tracer.parseLevel(envImpl,EnvironmentParams.JE_LOGGING_LEVEL_EVICTOR);
    original(envImpl);
  }
}
