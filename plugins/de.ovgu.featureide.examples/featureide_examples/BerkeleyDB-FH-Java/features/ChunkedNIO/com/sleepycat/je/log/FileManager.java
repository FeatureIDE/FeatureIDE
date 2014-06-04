package com.sleepycat.je.log;
public class FileManager {
  private long chunkedNIOSize=0;
  protected void hook456(  DbConfigManager configManager) throws DatabaseException {
    chunkedNIOSize=configManager.getLong(EnvironmentParams.LOG_CHUNKED_NIO);
    original(configManager);
  }
}
