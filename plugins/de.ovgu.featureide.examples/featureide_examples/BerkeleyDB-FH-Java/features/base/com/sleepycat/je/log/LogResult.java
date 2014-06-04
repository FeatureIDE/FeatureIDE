package com.sleepycat.je.log;
import de.ovgu.cide.jakutil.*;
class LogResult {
  long currentLsn;
  boolean wakeupCleaner;
  LogResult(  long currentLsn,  boolean wakeupCheckpointer,  boolean wakeupCleaner){
    this.currentLsn=currentLsn;
    this.hook510(wakeupCheckpointer);
    this.wakeupCleaner=wakeupCleaner;
  }
  protected void hook510(  boolean wakeupCheckpointer){
  }
}
