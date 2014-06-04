package com.sleepycat.je.log;
import java.io.IOException;
import java.nio.Buffer;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.utilint.DbLsn;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
/** 
 * A FileReader is an abstract class that traverses the log files, reading in
 * chunks of the file at a time. Concrete subclasses perform a particular action
 * to each entry.
 */
public abstract class FileReader {
  protected EnvironmentImpl env;
  protected FileManager fileManager;
  private ByteBuffer readBuffer;
  private ByteBuffer saveBuffer;
  private int maxReadBufferSize;
  private boolean singleFile;
  protected boolean eof;
  private boolean forward;
  protected long readBufferFileNum;
  protected long readBufferFileStart;
  protected long readBufferFileEnd;
  private int nRead;
  private long nRepeatIteratorReads;
  protected byte currentEntryTypeNum;
  protected byte currentEntryTypeVersion;
  protected long currentEntryPrevOffset;
  protected int currentEntrySize;
  protected long currentEntryChecksum;
  protected long currentEntryOffset;
  protected long nextEntryOffset;
  protected long startLsn;
  private long finishLsn;
  protected boolean anticipateChecksumErrors;
  /** 
 * A FileReader just needs to know what size chunks to read in.
 * @param endOfFileLsnindicates the end of the log file
 */
  public FileReader(  EnvironmentImpl env,  int readBufferSize,  boolean forward,  long startLsn,  Long singleFileNumber,  long endOfFileLsn,  long finishLsn) throws IOException, DatabaseException {
    this.env=env;
    this.fileManager=env.getFileManager();
    this.hook473(env);
    this.singleFile=(singleFileNumber != null);
    this.forward=forward;
    readBuffer=ByteBuffer.allocate(readBufferSize);
    threadSafeBufferFlip(readBuffer);
    saveBuffer=ByteBuffer.allocate(readBufferSize);
    DbConfigManager configManager=env.getConfigManager();
    maxReadBufferSize=configManager.getInt(EnvironmentParams.LOG_ITERATOR_MAX_SIZE);
    this.startLsn=startLsn;
    this.finishLsn=finishLsn;
    initStartingPosition(endOfFileLsn,singleFileNumber);
    nRead=0;
    this.hook472();
    anticipateChecksumErrors=false;
  }
  /** 
 * Helper for determining the starting position and opening up a file at the
 * desired location.
 */
  protected void initStartingPosition(  long endOfFileLsn,  Long ignoreSingleFileNumber) throws IOException, DatabaseException {
    eof=false;
    if (forward) {
      if (startLsn != DbLsn.NULL_LSN) {
        readBufferFileNum=DbLsn.getFileNumber(startLsn);
        readBufferFileEnd=DbLsn.getFileOffset(startLsn);
      }
 else {
        Long firstNum=fileManager.getFirstFileNum();
        if (firstNum == null) {
          eof=true;
        }
 else {
          readBufferFileNum=firstNum.longValue();
          readBufferFileEnd=0;
        }
      }
      nextEntryOffset=readBufferFileEnd;
    }
 else {
      assert startLsn != DbLsn.NULL_LSN;
      readBufferFileNum=DbLsn.getFileNumber(endOfFileLsn);
      readBufferFileStart=DbLsn.getFileOffset(endOfFileLsn);
      readBufferFileEnd=readBufferFileStart;
      if (DbLsn.getFileNumber(startLsn) == DbLsn.getFileNumber(endOfFileLsn)) {
        currentEntryPrevOffset=DbLsn.getFileOffset(startLsn);
      }
 else {
        currentEntryPrevOffset=0;
      }
      currentEntryOffset=DbLsn.getFileOffset(endOfFileLsn);
    }
  }
  /** 
 * @return the number of entries processed by this reader.
 */
  public int getNumRead(){
    return nRead;
  }
  public long getNRepeatIteratorReads(){
    return nRepeatIteratorReads;
  }
  /** 
 * Get LSN of the last entry read.
 */
  public long getLastLsn(){
    return DbLsn.makeLsn(readBufferFileNum,currentEntryOffset);
  }
  /** 
 * readNextEntry scans the log files until either it's reached the end of
 * the log or has hit an invalid portion. It then returns false.
 * @return true if an element has been read
 */
  public boolean readNextEntry() throws DatabaseException, IOException {
    return new FileReader_readNextEntry(this).execute();
  }
  protected boolean resyncReader(  long nextGoodRecordPostCorruption,  boolean dumpCorruptedBounds) throws DatabaseException, IOException {
    return false;
  }
  /** 
 * Make sure that the start of the target log entry is in the header. This
 * is a no-op if we're reading forwards
 */
  private void getLogEntryInReadBuffer() throws IOException, DatabaseException, EOFException {
    if (!forward) {
      if ((currentEntryPrevOffset != 0) && (currentEntryPrevOffset >= readBufferFileStart)) {
        long nextLsn=DbLsn.makeLsn(readBufferFileNum,currentEntryPrevOffset);
        if (finishLsn != DbLsn.NULL_LSN) {
          if (DbLsn.compareTo(nextLsn,finishLsn) == -1) {
            throw new EOFException();
          }
        }
        threadSafeBufferPosition(readBuffer,(int)(currentEntryPrevOffset - readBufferFileStart));
      }
 else {
        if (currentEntryPrevOffset == 0) {
          currentEntryPrevOffset=fileManager.getFileHeaderPrevOffset(readBufferFileNum);
          Long prevFileNum=fileManager.getFollowingFileNum(readBufferFileNum,false);
          if (prevFileNum == null) {
            throw new EOFException();
          }
          if (readBufferFileNum - prevFileNum.longValue() != 1) {
            if (!resyncReader(DbLsn.makeLsn(prevFileNum.longValue(),DbLsn.MAX_FILE_OFFSET),false)) {
              throw new DatabaseException("Cannot read backward over cleaned file" + " from " + readBufferFileNum + " to "+ prevFileNum);
            }
          }
          readBufferFileNum=prevFileNum.longValue();
          readBufferFileStart=currentEntryPrevOffset;
        }
 else         if ((currentEntryOffset - currentEntryPrevOffset) > readBuffer.capacity()) {
          readBufferFileStart=currentEntryPrevOffset;
        }
 else {
          long newPosition=currentEntryOffset - readBuffer.capacity();
          readBufferFileStart=(newPosition < 0) ? 0 : newPosition;
        }
        long nextLsn=DbLsn.makeLsn(readBufferFileNum,currentEntryPrevOffset);
        if (finishLsn != DbLsn.NULL_LSN) {
          if (DbLsn.compareTo(nextLsn,finishLsn) == -1) {
            throw new EOFException();
          }
        }
        FileHandle fileHandle=fileManager.getFileHandle(readBufferFileNum);
        this.hook469(fileHandle);
        readBufferFileEnd=readBufferFileStart + threadSafeBufferPosition(readBuffer);
        threadSafeBufferFlip(readBuffer);
        threadSafeBufferPosition(readBuffer,(int)(currentEntryPrevOffset - readBufferFileStart));
      }
      currentEntryOffset=currentEntryPrevOffset;
    }
 else {
      if (finishLsn != DbLsn.NULL_LSN) {
        long nextLsn=DbLsn.makeLsn(readBufferFileNum,nextEntryOffset);
        if (DbLsn.compareTo(nextLsn,finishLsn) >= 0) {
          throw new EOFException();
        }
      }
    }
  }
  /** 
 * Read the log entry header, leaving the buffer mark at the beginning of
 * the checksummed header data.
 */
  private void readHeader(  ByteBuffer dataBuffer) throws DatabaseException {
    currentEntryChecksum=LogUtils.getUnsignedInt(dataBuffer);
    dataBuffer.mark();
    currentEntryTypeNum=dataBuffer.get();
    if (!LogEntryType.isValidType(currentEntryTypeNum))     throw new DbChecksumException((anticipateChecksumErrors ? null : env),"FileReader read invalid log entry type: " + currentEntryTypeNum);
    currentEntryTypeVersion=dataBuffer.get();
    currentEntryPrevOffset=LogUtils.getUnsignedInt(dataBuffer);
    currentEntrySize=LogUtils.readInt(dataBuffer);
  }
  /** 
 * Try to read a specified number of bytes.
 * @param amountToReadis the number of bytes we need
 * @param collectDatais true if we need to actually look at the data. If false, we
 * know we're skipping this entry, and all we need to do is to
 * count until we get to the right spot.
 * @return a byte buffer positioned at the head of the desired portion, or
 * null if we reached eof.
 */
  private ByteBuffer readData(  int amountToRead,  boolean collectData) throws IOException, DatabaseException, EOFException {
    int alreadyRead=0;
    ByteBuffer completeBuffer=null;
    saveBuffer.clear();
    while ((alreadyRead < amountToRead) && !eof) {
      int bytesNeeded=amountToRead - alreadyRead;
      if (readBuffer.hasRemaining()) {
        if (collectData) {
          if ((alreadyRead > 0) || (readBuffer.remaining() < bytesNeeded)) {
            copyToSaveBuffer(bytesNeeded);
            alreadyRead=threadSafeBufferPosition(saveBuffer);
            completeBuffer=saveBuffer;
          }
 else {
            completeBuffer=readBuffer;
            alreadyRead=amountToRead;
          }
        }
 else {
          int positionIncrement=(readBuffer.remaining() > bytesNeeded) ? bytesNeeded : readBuffer.remaining();
          alreadyRead+=positionIncrement;
          threadSafeBufferPosition(readBuffer,threadSafeBufferPosition(readBuffer) + positionIncrement);
          completeBuffer=readBuffer;
        }
      }
 else {
        fillReadBuffer(bytesNeeded);
      }
    }
    threadSafeBufferFlip(saveBuffer);
    return completeBuffer;
  }
  /** 
 * Change the read buffer size if we start hitting large log entries so we
 * don't get into an expensive cycle of multiple reads and piecing together
 * of log entries.
 */
  private void adjustReadBufferSize(  int amountToRead){
    int readBufferSize=readBuffer.capacity();
    if (amountToRead > readBufferSize) {
      if (readBufferSize < maxReadBufferSize) {
        if (amountToRead < maxReadBufferSize) {
          readBufferSize=amountToRead;
          int remainder=readBufferSize % 1024;
          readBufferSize+=1024 - remainder;
          readBufferSize=Math.min(readBufferSize,maxReadBufferSize);
        }
 else {
          readBufferSize=maxReadBufferSize;
        }
        readBuffer=ByteBuffer.allocate(readBufferSize);
      }
      if (amountToRead > readBuffer.capacity()) {
        nRepeatIteratorReads++;
      }
    }
  }
  /** 
 * Copy the required number of bytes into the save buffer.
 */
  private void copyToSaveBuffer(  int bytesNeeded){
    int bytesFromThisBuffer;
    if (bytesNeeded <= readBuffer.remaining()) {
      bytesFromThisBuffer=bytesNeeded;
    }
 else {
      bytesFromThisBuffer=readBuffer.remaining();
    }
    ByteBuffer temp;
    if (saveBuffer.capacity() - threadSafeBufferPosition(saveBuffer) < bytesFromThisBuffer) {
      temp=ByteBuffer.allocate(saveBuffer.capacity() + bytesFromThisBuffer);
      threadSafeBufferFlip(saveBuffer);
      temp.put(saveBuffer);
      saveBuffer=temp;
    }
    temp=readBuffer.slice();
    temp.limit(bytesFromThisBuffer);
    saveBuffer.put(temp);
    threadSafeBufferPosition(readBuffer,threadSafeBufferPosition(readBuffer) + bytesFromThisBuffer);
  }
  /** 
 * Fill up the read buffer with more data.
 */
  private void fillReadBuffer(  int bytesNeeded) throws DatabaseException, EOFException {
    FileHandle fileHandle=null;
    try {
      adjustReadBufferSize(bytesNeeded);
      fileHandle=fileManager.getFileHandle(readBufferFileNum);
      boolean fileOk=false;
      if (readBufferFileEnd < fileHandle.getFile().length()) {
        fileOk=true;
      }
 else {
        if (!singleFile) {
          Long nextFile=fileManager.getFollowingFileNum(readBufferFileNum,forward);
          if (nextFile != null) {
            readBufferFileNum=nextFile.longValue();
            this.hook470(fileHandle);
            fileHandle=fileManager.getFileHandle(readBufferFileNum);
            fileOk=true;
            readBufferFileEnd=0;
            nextEntryOffset=0;
          }
        }
      }
      if (fileOk) {
        readBuffer.clear();
        fileManager.readFromFile(fileHandle.getFile(),readBuffer,readBufferFileEnd);
        assert EnvironmentImpl.maybeForceYield();
        readBufferFileStart=readBufferFileEnd;
        readBufferFileEnd=readBufferFileStart + threadSafeBufferPosition(readBuffer);
        threadSafeBufferFlip(readBuffer);
      }
 else {
        throw new EOFException();
      }
    }
 catch (    IOException e) {
      e.printStackTrace();
      throw new DatabaseException("Problem in fillReadBuffer, readBufferFileNum = " + readBufferFileNum + ": "+ e.getMessage());
    }
 finally {
      this.hook471(fileHandle);
    }
  }
  /** 
 * @return true if this reader should process this entry, or just skip over
 * it.
 */
  protected boolean isTargetEntry(  byte logEntryTypeNumber,  byte logEntryTypeVersion) throws DatabaseException {
    return true;
  }
  /** 
 * Each file reader implements this method to process the entry data.
 * @param enteryBuffercontains the entry data and is positioned at the data
 * @return true if this entry should be returned
 */
  protected abstract boolean processEntry(  ByteBuffer entryBuffer) throws DatabaseException ;
private static class EOFException extends Exception {
  }
  /** 
 * Note that we catch Exception here because it is possible that another
 * thread is modifying the state of buffer simultaneously. Specifically,
 * this can happen if another thread is writing this log buffer out and it
 * does (e.g.) a flip operation on it. The actual mark/pos of the buffer may
 * be caught in an unpredictable state. We could add another latch to
 * protect this buffer, but that's heavier weight than we need. So the
 * easiest thing to do is to just retry the duplicate operation. See
 * [#9822].
 */
  private Buffer threadSafeBufferFlip(  ByteBuffer buffer){
    while (true) {
      try {
        return buffer.flip();
      }
 catch (      IllegalArgumentException IAE) {
        continue;
      }
    }
  }
  private int threadSafeBufferPosition(  ByteBuffer buffer){
    while (true) {
      try {
        return buffer.position();
      }
 catch (      IllegalArgumentException IAE) {
        continue;
      }
    }
  }
  private Buffer threadSafeBufferPosition(  ByteBuffer buffer,  int newPosition){
    while (true) {
      try {
        return buffer.position(newPosition);
      }
 catch (      IllegalArgumentException IAE) {
        continue;
      }
    }
  }
@MethodObject static class FileReader_readNextEntry {
    FileReader_readNextEntry(    FileReader _this){
      this._this=_this;
    }
    boolean execute() throws DatabaseException, IOException {
      foundEntry=false;
      try {
        while ((!_this.eof) && (!foundEntry)) {
          _this.getLogEntryInReadBuffer();
          dataBuffer=_this.readData(LogManager.HEADER_BYTES,true);
          _this.readHeader(dataBuffer);
          isTargetEntry=_this.isTargetEntry(_this.currentEntryTypeNum,_this.currentEntryTypeVersion);
          this.hook476();
          collectData=isTargetEntry;
          this.hook475();
          dataBuffer=_this.readData(_this.currentEntrySize,collectData);
          if (_this.forward) {
            _this.currentEntryOffset=_this.nextEntryOffset;
            _this.nextEntryOffset+=LogManager.HEADER_BYTES + _this.currentEntrySize;
          }
          this.hook474();
          if (isTargetEntry) {
            if (_this.processEntry(dataBuffer)) {
              foundEntry=true;
              _this.nRead++;
            }
          }
 else           if (collectData) {
            _this.threadSafeBufferPosition(dataBuffer,_this.threadSafeBufferPosition(dataBuffer) + _this.currentEntrySize);
          }
        }
      }
 catch (      EOFException e) {
        _this.eof=true;
      }
catch (      DatabaseException e) {
        this.hook468();
        throw e;
      }
      return foundEntry;
    }
    protected FileReader _this;
    protected boolean foundEntry;
    protected ByteBuffer dataBuffer;
    protected boolean isTargetEntry;
    protected boolean doValidate;
    protected boolean collectData;
    protected LogEntryType problemType;
    protected void hook468() throws DatabaseException, IOException {
    }
    protected void hook474() throws DatabaseException, IOException, EOFException {
    }
    protected void hook475() throws DatabaseException, IOException, EOFException {
    }
    protected void hook476() throws DatabaseException, IOException, EOFException {
    }
  }
  protected void hook469(  FileHandle fileHandle) throws IOException, DatabaseException, EOFException {
    readBuffer.clear();
    fileManager.readFromFile(fileHandle.getFile(),readBuffer,readBufferFileStart);
    assert EnvironmentImpl.maybeForceYield();
  }
  protected void hook470(  FileHandle fileHandle) throws DatabaseException, EOFException, IOException {
  }
  protected void hook471(  FileHandle fileHandle) throws DatabaseException, EOFException {
  }
  protected void hook472() throws IOException, DatabaseException {
  }
  protected void hook473(  EnvironmentImpl env) throws IOException, DatabaseException {
  }
}
