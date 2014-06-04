package com.sleepycat.je.log;
public class LastFileReader {
  protected void hook477(  FileHandle fileHandle) throws IOException, DatabaseException {
    fileHandle.release();
    original(fileHandle);
  }
  protected void hook478(  FileHandle fileHandle) throws IOException, DatabaseException {
    if (fileHandle != null) {
      fileHandle.release();
    }
    original(fileHandle);
  }
}
