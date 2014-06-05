package com.sleepycat.je.recovery;
public class Checkpointer extends DaemonThread {
  public String toString(){
    StringBuffer sb=new StringBuffer();
    sb.append("<Checkpointer name=\"").append(name).append("\"/>");
    return sb.toString();
  }
  synchronized public void clearEnv(){
    envImpl=null;
  }
  /** 
 * Return the number of retries when a deadlock exception occurs.
 */
  protected int nDeadlockRetries() throws DatabaseException {
    return envImpl.getConfigManager().getInt(EnvironmentParams.CHECKPOINTER_RETRY);
  }
  /** 
 * Called whenever the DaemonThread wakes up from a sleep.
 */
  protected void onWakeup() throws DatabaseException {
    if (envImpl.isClosed()) {
      return;
    }
    doCheckpoint(CheckpointConfig.DEFAULT,false,"daemon");
  }
  protected void hook538(  EnvironmentImpl envImpl,  long waitTime,  String name) throws DatabaseException {
    super.init(0 + waitTime,name,envImpl);
    original(envImpl,waitTime,name);
  }
}
