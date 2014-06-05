package com.sleepycat.je.log;
abstract public class LogManager {
  protected void hook501(  boolean fsyncRequired) throws DatabaseException {
    if (fsyncRequired) {
      fileManager.groupSync();
    }
    original(fsyncRequired);
  }
}
