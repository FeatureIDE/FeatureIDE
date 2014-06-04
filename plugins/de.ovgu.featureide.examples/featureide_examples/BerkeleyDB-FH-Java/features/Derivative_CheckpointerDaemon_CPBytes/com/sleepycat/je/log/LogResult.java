package com.sleepycat.je.log;
class LogResult {
  boolean wakeupCheckpointer;
  protected void hook510(  boolean wakeupCheckpointer){
    this.wakeupCheckpointer=wakeupCheckpointer;
    original(wakeupCheckpointer);
  }
}
