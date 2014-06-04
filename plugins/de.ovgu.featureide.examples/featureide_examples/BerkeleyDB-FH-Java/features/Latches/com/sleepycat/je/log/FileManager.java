package com.sleepycat.je.log;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
public class FileManager {
  protected void hook453(  FileHandle fileHandle) throws LogException, DatabaseException {
    fileHandle.latch();
    original(fileHandle);
  }
  protected void hook454(  FileHandle fileHandle) throws LogException, DatabaseException {
    fileHandle.release();
    original(fileHandle);
  }
}
