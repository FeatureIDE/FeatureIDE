package com.sleepycat.je.evictor;
public class Evictor extends DaemonThread {
  /** 
 * Evictor doesn't have a work queue so just throw an exception if it's ever
 * called.
 */
  public void addToQueue(  Object o) throws DatabaseException {
    throw new DatabaseException("Evictor.addToQueue should never be called.");
  }
  /** 
 * Return the number of retries when a deadlock exception occurs.
 */
  protected int nDeadlockRetries() throws DatabaseException {
    return envImpl.getConfigManager().getInt(EnvironmentParams.EVICTOR_RETRY);
  }
  /** 
 * Called whenever the daemon thread wakes up from a sleep.
 */
  public void onWakeup() throws DatabaseException {
    if (envImpl.isClosed()) {
      return;
    }
    doEvict(SOURCE_DAEMON,false);
  }
}
