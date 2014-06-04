package com.sleepycat.je.log;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.HashSet;
import java.util.Set;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.log.entry.LogEntry;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * A ScavengerFileReader reads the log backwards.  If it encounters a checksum
 * error, it goes to the start of that log file and reads forward until it
 * encounters a checksum error.  It then continues the reading backwards in the
 * log.
 * The caller may set "dumpCorruptedBounds" to true if information about the
 * start and finish of the corrupted portion should be displayed on stderr.
 * The caller is expected to implement processEntryCallback. This method is
 * called once for each entry that the ScavengerFileReader finds in the log.
 */
abstract public class ScavengerFileReader extends FileReader {
  private Set targetEntryTypes;
  private int readBufferSize;
  private boolean dumpCorruptedBounds;
  /** 
 * Create this reader to start at a given LSN.
 */
  public ScavengerFileReader(  EnvironmentImpl env,  int readBufferSize,  long startLsn,  long finishLsn,  long endOfFileLsn) throws IOException, DatabaseException {
    super(env,readBufferSize,false,startLsn,null,endOfFileLsn,finishLsn);
    this.readBufferSize=readBufferSize;
    anticipateChecksumErrors=true;
    targetEntryTypes=new HashSet();
    dumpCorruptedBounds=false;
  }
  /** 
 * Set to true if corrupted boundaries should be dumped to stderr.
 */
  public void setDumpCorruptedBounds(  boolean dumpCorruptedBounds){
    this.dumpCorruptedBounds=dumpCorruptedBounds;
  }
  /** 
 * Tell the reader that we are interested in these kind of entries.
 */
  public void setTargetType(  LogEntryType type){
    targetEntryTypes.add(new Byte(type.getTypeNum()));
  }
  protected boolean processEntry(  ByteBuffer entryBuffer) throws DatabaseException {
    LogEntryType lastEntryType=LogEntryType.findType(currentEntryTypeNum,currentEntryTypeVersion);
    LogEntry entry=lastEntryType.getSharedLogEntry();
    entry.readEntry(entryBuffer,currentEntrySize,currentEntryTypeVersion,true);
    processEntryCallback(entry,lastEntryType);
    return true;
  }
  abstract protected void processEntryCallback(  LogEntry entry,  LogEntryType entryType) throws DatabaseException ;
  public boolean readNextEntry() throws DatabaseException, IOException {
    long saveCurrentEntryOffset=currentEntryOffset;
    try {
      return super.readNextEntry();
    }
 catch (    DbChecksumException DCE) {
      resyncReader(DbLsn.makeLsn(readBufferFileNum,saveCurrentEntryOffset),dumpCorruptedBounds);
      return super.readNextEntry();
    }
  }
  protected boolean resyncReader(  long nextGoodRecordPostCorruption,  boolean showCorruptedBounds) throws DatabaseException, IOException {
    LastFileReader reader=null;
    long tryReadBufferFileNum=DbLsn.getFileNumber(nextGoodRecordPostCorruption);
    while (tryReadBufferFileNum >= 0) {
      try {
        reader=new LastFileReader(env,readBufferSize,new Long(tryReadBufferFileNum));
        break;
      }
 catch (      DbChecksumException DCE) {
        tryReadBufferFileNum--;
        continue;
      }
    }
    boolean switchedFiles=tryReadBufferFileNum != DbLsn.getFileNumber(nextGoodRecordPostCorruption);
    if (!switchedFiles) {
      while (reader.readNextEntry()) {
      }
    }
    long lastUsedLsn=reader.getLastValidLsn();
    long nextAvailableLsn=reader.getEndOfLog();
    if (showCorruptedBounds) {
      System.err.println("A checksum error was found in the log.");
      System.err.println("Corruption begins at LSN:\n   " + DbLsn.toString(nextAvailableLsn));
      System.err.println("Last known good record before corruption is at LSN:\n   " + DbLsn.toString(lastUsedLsn));
      System.err.println("Next known good record after corruption is at LSN:\n   " + DbLsn.toString(nextGoodRecordPostCorruption));
    }
    startLsn=lastUsedLsn;
    initStartingPosition(nextAvailableLsn,null);
    if (switchedFiles) {
      currentEntryPrevOffset=0;
    }
    return true;
  }
  /** 
 * @return true if this reader should process this entry, or just skip
 * over it.
 */
  protected boolean isTargetEntry(  byte logEntryTypeNumber,  byte logEntryTypeVersion){
    if (targetEntryTypes.size() == 0) {
      return true;
    }
 else {
      return targetEntryTypes.contains(new Byte(logEntryTypeNumber));
    }
  }
}
