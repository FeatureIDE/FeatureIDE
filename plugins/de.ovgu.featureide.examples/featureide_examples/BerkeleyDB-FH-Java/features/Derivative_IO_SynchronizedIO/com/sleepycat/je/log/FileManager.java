package com.sleepycat.je.log;
public class FileManager {
@MethodObject static class FileManager_writeToFile {
    protected void hook447() throws IOException, DatabaseException {
synchronized (file) {
        original();
      }
    }
  }
@MethodObject static class FileManager_readFromFile {
    protected void hook448() throws IOException {
synchronized (file) {
        original();
      }
    }
  }
}
