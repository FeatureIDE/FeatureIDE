package com.sleepycat.je.log;
public abstract class FileReader {
  protected void hook469(  FileHandle fileHandle) throws IOException, DatabaseException, EOFException {
    try {
      original(fileHandle);
    }
  finally {
      fileHandle.release();
    }
  }
  protected void hook470(  FileHandle fileHandle) throws DatabaseException, EOFException, IOException {
    fileHandle.release();
    original(fileHandle);
  }
  protected void hook471(  FileHandle fileHandle) throws DatabaseException, EOFException {
    if (fileHandle != null) {
      fileHandle.release();
    }
    original(fileHandle);
  }
}
