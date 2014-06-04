package com.sleepycat.je.cleaner;
class FileProcessor {
@MethodObject static class FileProcessor_processFile {
    protected void hook137() throws DatabaseException, IOException {
      reader.setAlwaysValidateChecksum(true);
      original();
    }
  }
}
