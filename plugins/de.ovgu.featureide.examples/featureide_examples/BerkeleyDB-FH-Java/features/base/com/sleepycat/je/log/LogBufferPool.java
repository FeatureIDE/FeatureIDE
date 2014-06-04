package com.sleepycat.je.log;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.Iterator;
import java.util.LinkedList;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * LogBufferPool keeps a set of log buffers.
 */
class LogBufferPool {
  private static final String DEBUG_NAME=LogBufferPool.class.getName();
  private EnvironmentImpl envImpl=null;
  private int logBufferSize;
  private LinkedList bufferPool;
  private LogBuffer currentWriteBuffer;
  private FileManager fileManager;
  private boolean runInMemory;
  LogBufferPool(  FileManager fileManager,  EnvironmentImpl envImpl) throws DatabaseException {
    this.fileManager=fileManager;
    this.envImpl=envImpl;
    this.hook485(envImpl);
    DbConfigManager configManager=envImpl.getConfigManager();
    runInMemory=configManager.getBoolean(EnvironmentParams.LOG_MEMORY_ONLY);
    reset(configManager);
    currentWriteBuffer=(LogBuffer)bufferPool.getFirst();
  }
  /** 
 * Initialize the pool at construction time and when the cache is resized.
 * This method is called after the memory budget has been calculated.
 */
  void reset(  DbConfigManager configManager) throws DatabaseException {
    if (runInMemory && bufferPool != null) {
      return;
    }
    int numBuffers=configManager.getInt(EnvironmentParams.NUM_LOG_BUFFERS);
    long logBufferBudget=envImpl.getMemoryBudget().getLogBufferBudget();
    int newBufferSize=(int)logBufferBudget / numBuffers;
    LinkedList newPool=new LinkedList();
    if (runInMemory) {
      numBuffers=1;
    }
    for (int i=0; i < numBuffers; i++) {
      newPool.add(new LogBuffer(newBufferSize,envImpl));
    }
    this.hook486();
    bufferPool=newPool;
    logBufferSize=newBufferSize;
  }
  /** 
 * Get a log buffer for writing sizeNeeded bytes. If currentWriteBuffer is
 * too small or too full, flush currentWriteBuffer and get a new one.
 * Called within the log write latch.
 * @return a buffer that can hold sizeNeeded bytes.
 */
  LogBuffer getWriteBuffer(  int sizeNeeded,  boolean flippedFile) throws IOException, DatabaseException {
    if ((!currentWriteBuffer.hasRoom(sizeNeeded)) || flippedFile) {
      writeBufferToFile(sizeNeeded);
    }
    if (flippedFile) {
      if (!runInMemory) {
        fileManager.syncLogEndAndFinishFile();
      }
    }
    return currentWriteBuffer;
  }
  /** 
 * Write the contents of the currentWriteBuffer to disk.  Leave this buffer
 * in memory to be available to would be readers.  Set up a new
 * currentWriteBuffer. Assumes the log write latch is held.
 * @param sizeNeeded is the size of the next object we need to write to
 * the log. May be 0 if this is called on behalf of LogManager.flush().
 */
  void writeBufferToFile(  int sizeNeeded) throws IOException, DatabaseException {
    int bufferSize=((logBufferSize > sizeNeeded) ? logBufferSize : sizeNeeded);
    this.hook488();
    LogBuffer latchedBuffer=currentWriteBuffer;
    this.hook487(bufferSize,latchedBuffer);
  }
  /** 
 * A loggable object has been freshly marshalled into the write log buffer.
 * 1. Update buffer so it knows what LSNs it contains.
 * 2. If this object requires a flush, write this buffer out to the 
 * backing file.
 * Assumes log write latch is held.
 */
  void writeCompleted(  long lsn,  boolean flushRequired) throws DatabaseException, IOException {
    currentWriteBuffer.registerLsn(lsn);
    if (flushRequired) {
      writeBufferToFile(0);
    }
  }
  /** 
 * Find a buffer that holds this LSN.
 * @return the buffer that contains this LSN, latched and ready to
 * read, or return null.
 */
  LogBuffer getReadBuffer(  long lsn) throws DatabaseException {
    LogBuffer foundBuffer=null;
    foundBuffer=this.hook489(lsn,foundBuffer);
    if (foundBuffer == null) {
      return null;
    }
 else {
      return foundBuffer;
    }
  }
  protected void hook485(  EnvironmentImpl envImpl) throws DatabaseException {
  }
  protected void hook486() throws DatabaseException {
  }
  protected void hook487(  int bufferSize,  LogBuffer latchedBuffer) throws IOException, DatabaseException {
    ByteBuffer currentByteBuffer=currentWriteBuffer.getDataBuffer();
    int savePosition=currentByteBuffer.position();
    int saveLimit=currentByteBuffer.limit();
    currentByteBuffer.flip();
    if (runInMemory) {
      this.hook492(latchedBuffer);
      latchedBuffer=null;
      this.hook491();
      currentWriteBuffer=new LogBuffer(bufferSize,envImpl);
      bufferPool.add(currentWriteBuffer);
      this.hook490();
    }
 else {
      try {
        fileManager.writeLogBuffer(currentWriteBuffer);
        currentWriteBuffer.getDataBuffer().rewind();
        this.hook494(latchedBuffer);
        latchedBuffer=null;
        LogBuffer nextToUse=null;
        this.hook493(nextToUse);
      }
 catch (      DatabaseException DE) {
        currentByteBuffer.position(savePosition);
        currentByteBuffer.limit(saveLimit);
        throw DE;
      }
    }
  }
  protected void hook488() throws IOException, DatabaseException {
  }
  protected LogBuffer hook489(  long lsn,  LogBuffer foundBuffer) throws DatabaseException {
    Iterator iter=bufferPool.iterator();
    while (iter.hasNext()) {
      LogBuffer l=(LogBuffer)iter.next();
      if (l.containsLsn(lsn)) {
        foundBuffer=l;
        break;
      }
    }
    if (foundBuffer == null && currentWriteBuffer.containsLsn(lsn)) {
      foundBuffer=currentWriteBuffer;
    }
    if (foundBuffer == null) {
      this.hook496();
    }
    return foundBuffer;
  }
  protected void hook490() throws IOException, DatabaseException {
  }
  protected void hook491() throws IOException, DatabaseException {
  }
  protected void hook492(  LogBuffer latchedBuffer) throws IOException, DatabaseException {
  }
  protected void hook493(  LogBuffer nextToUse) throws IOException, DatabaseException {
    this.hook495();
    Iterator iter=bufferPool.iterator();
    nextToUse=(LogBuffer)iter.next();
    boolean done=bufferPool.remove(nextToUse);
    assert done;
    nextToUse.reinit();
    bufferPool.add(nextToUse);
    currentWriteBuffer=nextToUse;
  }
  protected void hook494(  LogBuffer latchedBuffer) throws IOException, DatabaseException {
  }
  protected void hook495() throws IOException, DatabaseException {
  }
  protected void hook496() throws DatabaseException {
  }
}
