package com.sleepycat.je.log;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * FileSource is used as a channel to a log file when faulting in objects
 * from the log.
 */
class FileSource implements LogSource {
  private RandomAccessFile file;
  private int readBufferSize;
  private FileManager fileManager;
  FileSource(  RandomAccessFile file,  int readBufferSize,  FileManager fileManager){
    this.file=file;
    this.readBufferSize=readBufferSize;
    this.fileManager=fileManager;
  }
  /** 
 * @see LogSource#release
 */
  public void release() throws DatabaseException {
  }
  /** 
 * @see LogSource#getBytes
 */
  public ByteBuffer getBytes(  long fileOffset) throws IOException {
    ByteBuffer destBuf=ByteBuffer.allocate(readBufferSize);
    fileManager.readFromFile(file,destBuf,fileOffset);
    assert EnvironmentImpl.maybeForceYield();
    destBuf.flip();
    return destBuf;
  }
  /** 
 * @see LogSource#getBytes
 */
  public ByteBuffer getBytes(  long fileOffset,  int numBytes) throws IOException {
    ByteBuffer destBuf=ByteBuffer.allocate(numBytes);
    fileManager.readFromFile(file,destBuf,fileOffset);
    assert EnvironmentImpl.maybeForceYield();
    destBuf.flip();
    assert destBuf.remaining() >= numBytes : "remaining=" + destBuf.remaining() + " numBytes="+ numBytes;
    return destBuf;
  }
}
