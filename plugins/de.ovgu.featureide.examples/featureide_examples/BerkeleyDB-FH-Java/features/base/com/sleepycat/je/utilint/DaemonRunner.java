package com.sleepycat.je.utilint;
import de.ovgu.cide.jakutil.*;
/** 
 * An object capable of running (run/pause/shutdown/etc) a daemon thread.
 * See DaemonThread for details.
 */
public interface DaemonRunner {
  void runOrPause(  boolean run);
  void requestShutdown();
  void shutdown();
  int getNWakeupRequests();
}
