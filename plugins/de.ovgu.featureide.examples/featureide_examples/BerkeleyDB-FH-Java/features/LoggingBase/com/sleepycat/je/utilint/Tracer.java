package com.sleepycat.je.utilint;
public class Tracer {
  /** 
 * Create trace record that will be filled in from the log.
 */
  Tracer(){
  }
  public String getMessage(){
    return msg;
  }
  /** 
 * Logger method for recording a general message.
 */
  public static void trace(  Level logLevel,  EnvironmentImpl envImpl,  String msg){
    envImpl.getLogger().log(logLevel,msg);
    original(logLevel,envImpl,msg);
  }
}
