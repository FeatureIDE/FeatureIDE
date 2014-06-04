package com.sleepycat.je.cleaner;
public class Cleaner implements DaemonRunner {
  public void runOrPause(  boolean run){
    if (!env.isNoLocking()) {
      for (int i=0; i < threads.length; i+=1) {
        if (threads[i] != null) {
          threads[i].runOrPause(run);
        }
      }
    }
  }
  public void requestShutdown(){
    for (int i=0; i < threads.length; i+=1) {
      if (threads[i] != null) {
        threads[i].requestShutdown();
      }
    }
  }
  public void shutdown(){
    for (int i=0; i < threads.length; i+=1) {
      if (threads[i] != null) {
        threads[i].shutdown();
        threads[i].clearEnv();
        threads[i]=null;
      }
    }
  }
  public int getNWakeupRequests(){
    int count=0;
    for (int i=0; i < threads.length; i+=1) {
      if (threads[i] != null) {
        count+=threads[i].getNWakeupRequests();
      }
    }
    return count;
  }
}
