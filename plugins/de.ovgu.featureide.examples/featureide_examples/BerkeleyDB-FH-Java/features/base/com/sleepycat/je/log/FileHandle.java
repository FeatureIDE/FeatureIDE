package com.sleepycat.je.log;
import java.io.IOException;
import java.io.RandomAccessFile;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * A FileHandle embodies a File and its accompanying latch.
 */
class FileHandle {
  private RandomAccessFile file;
  private boolean oldHeaderVersion;
  FileHandle(  RandomAccessFile file,  String fileName,  EnvironmentImpl env,  boolean oldHeaderVersion){
    this.file=file;
    this.oldHeaderVersion=oldHeaderVersion;
    this.hook444(fileName,env);
  }
  RandomAccessFile getFile(){
    return file;
  }
  boolean isOldHeaderVersion(){
    return oldHeaderVersion;
  }
  void close() throws IOException {
    if (file != null) {
      file.close();
      file=null;
    }
  }
  protected void hook444(  String fileName,  EnvironmentImpl env){
  }
}
