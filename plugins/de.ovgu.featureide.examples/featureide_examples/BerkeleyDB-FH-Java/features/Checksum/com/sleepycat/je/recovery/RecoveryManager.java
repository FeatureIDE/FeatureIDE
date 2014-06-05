package com.sleepycat.je.recovery;
public class RecoveryManager {
  protected void hook593(  INFileReader reader) throws IOException, DatabaseException {
    reader.setAlwaysValidateChecksum(true);
    original(reader);
  }
}
