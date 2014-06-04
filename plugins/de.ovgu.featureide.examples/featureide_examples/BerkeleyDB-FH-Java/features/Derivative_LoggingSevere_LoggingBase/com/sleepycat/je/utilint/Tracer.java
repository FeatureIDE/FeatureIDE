package com.sleepycat.je.utilint;
public class Tracer {
  /** 
 * Logger method for recording an exception and stacktrace.
 */
  public static void trace(  EnvironmentImpl envImpl,  String sourceClass,  String sourceMethod,  String msg,  Throwable t){
    envImpl.getLogger().logp(Level.SEVERE,sourceClass,sourceMethod,msg + "\n" + Tracer.getStackTrace(t));
    original(envImpl,sourceClass,sourceMethod,msg,t);
  }
}
