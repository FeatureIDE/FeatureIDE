package com.sleepycat.je.utilint;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DeadlockException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * A daemon thread.
 */
public abstract class DaemonThread implements DaemonRunner, Runnable {
  private static final int JOIN_MILLIS=10;
  private long waitTime;
  private Object synchronizer=new Object();
  private Thread thread;
  private EnvironmentImpl env;
  protected String name;
  protected Set workQueue;
  protected int nWakeupRequests;
  private volatile boolean shutdownRequest=false;
  private volatile boolean paused=false;
  private boolean running=false;
  protected DaemonThread(){
  }
  public DaemonThread(  long waitTime,  String name,  EnvironmentImpl env){
    init(waitTime,name,env);
  }
  protected void init(  long waitTime,  String name,  EnvironmentImpl env){
    this.waitTime=waitTime;
    this.name=name;
    this.env=env;
    workQueue=new HashSet();
    this.hook856(name,env);
  }
  /** 
 * For testing.
 */
  public Thread getThread(){
    return thread;
  }
  /** 
 * If run is true, starts the thread if not started or unpauses it if
 * already started; if run is false, pauses the thread if started or does
 * nothing if not started.
 */
  public void runOrPause(  boolean run){
    if (run) {
      paused=false;
      if (thread != null) {
        wakeup();
      }
 else {
        thread=new Thread(this,name);
        thread.setDaemon(true);
        thread.start();
      }
    }
 else {
      paused=true;
    }
  }
  public void requestShutdown(){
    shutdownRequest=true;
  }
  /** 
 * Requests shutdown and calls join() to wait for the thread to stop.
 */
  public void shutdown(){
    if (thread != null) {
      shutdownRequest=true;
      while (thread.isAlive()) {
synchronized (synchronizer) {
          synchronizer.notifyAll();
        }
        try {
          thread.join(JOIN_MILLIS);
        }
 catch (        InterruptedException e) {
        }
      }
      thread=null;
    }
  }
  public String toString(){
    StringBuffer sb=new StringBuffer();
    sb.append("<DaemonThread name=\"").append(name).append("\"/>");
    return sb.toString();
  }
  public void addToQueue(  Object o) throws DatabaseException {
    workQueue.add(o);
    wakeup();
  }
  public int getQueueSize() throws DatabaseException {
    int count=workQueue.size();
    return count;
  }
  public void addToQueueAlreadyLatched(  Collection c) throws DatabaseException {
    workQueue.addAll(c);
  }
  public void wakeup(){
    if (!paused) {
synchronized (synchronizer) {
        synchronizer.notifyAll();
      }
    }
  }
  public void run(){
    while (true) {
      if (shutdownRequest) {
        break;
      }
      try {
        this.hook858();
        boolean nothingToDo=workQueue.size() == 0;
        this.hook857();
        if (nothingToDo) {
synchronized (synchronizer) {
            if (waitTime == 0) {
              synchronizer.wait();
            }
 else {
              synchronizer.wait(waitTime);
            }
          }
        }
        if (shutdownRequest) {
          break;
        }
        if (paused) {
synchronized (synchronizer) {
            synchronizer.wait();
          }
          continue;
        }
        int numTries=0;
        int maxRetries=nDeadlockRetries();
        do {
          try {
            nWakeupRequests++;
            running=true;
            onWakeup();
            break;
          }
 catch (          DeadlockException e) {
          }
 finally {
            running=false;
          }
          numTries++;
          if (shutdownRequest) {
            break;
          }
        }
 while (numTries <= maxRetries);
        if (shutdownRequest) {
          break;
        }
      }
 catch (      InterruptedException IE) {
        System.err.println("Shutting down " + this + " due to exception: "+ IE);
        shutdownRequest=true;
      }
catch (      Exception E) {
        System.err.println(this + " caught exception: " + E);
        E.printStackTrace(System.err);
        if (env.mayNotWrite()) {
          System.err.println("Exiting");
          shutdownRequest=true;
        }
 else {
          System.err.println("Continuing");
        }
      }
    }
  }
  /** 
 * Returns the number of retries to perform when Deadlock Exceptions occur.
 */
  protected int nDeadlockRetries() throws DatabaseException {
    return 0;
  }
  /** 
 * onWakeup is synchronized to ensure that multiple invocations of the
 * DaemonThread aren't made. isRunnable must be called from within onWakeup
 * to avoid having the following sequence: Thread A: isRunnable() => true,
 * Thread B: isRunnable() => true, Thread A: onWakeup() starts Thread B:
 * waits for monitor on thread to call onWakeup() Thread A: onWakeup()
 * completes rendering isRunnable() predicate false Thread B: onWakeup()
 * starts, but isRunnable predicate is now false
 */
  abstract protected void onWakeup() throws DatabaseException ;
  /** 
 * Returns whether shutdown has been requested. This method should be used
 * to to terminate daemon loops.
 */
  protected boolean isShutdownRequested(){
    return shutdownRequest;
  }
  /** 
 * Returns whether the onWakeup method is currently executing. This is only
 * an approximation and is used to avoid unnecessary wakeups.
 */
  public boolean isRunning(){
    return running;
  }
  /** 
 * For unit testing.
 */
  public int getNWakeupRequests(){
    return nWakeupRequests;
  }
  protected void hook856(  String name,  EnvironmentImpl env){
  }
  protected void hook857() throws InterruptedException, Exception {
  }
  protected void hook858() throws InterruptedException, Exception {
  }
}
