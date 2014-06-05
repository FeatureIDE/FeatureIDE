package com.sleepycat.je.log;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import java.nio.channels.ClosedChannelException;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.channels.OverlappingFileLockException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.zip.Checksum;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.RunRecoveryException;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.log.entry.LogEntry;
import com.sleepycat.je.utilint.Adler32;
import com.sleepycat.je.utilint.DbLsn;
import com.sleepycat.je.utilint.HexFormatter;
import de.ovgu.cide.jakutil.*;
/** 
 * The FileManager presents the abstraction of one contiguous file. It doles out
 * LSNs.
 */
public class FileManager {
public static class FileMode {
    public static final FileMode READ_MODE=new FileMode("r");
    public static final FileMode READWRITE_MODE=new FileMode("rw");
    private String fileModeValue;
    private FileMode(    String fileModeValue){
      this.fileModeValue=fileModeValue;
    }
    public String getModeValue(){
      return fileModeValue;
    }
  }
  static boolean IO_EXCEPTION_TESTING=false;
  private static final String DEBUG_NAME=FileManager.class.getName();
  private static long writeCount=0;
  private static long stopOnWriteCount=Long.MAX_VALUE;
  public static final String JE_SUFFIX=".jdb";
  public static final String CIF_SUFFIX=".cif";
  public static final String DEL_SUFFIX=".del";
  public static final String BAD_SUFFIX=".bad";
  public static final String LOCK_SUFFIX=".lck";
  static final String[] DEL_SUFFIXES={DEL_SUFFIX};
  static final String[] JE_SUFFIXES={JE_SUFFIX};
  private static final String[] JE_AND_DEL_SUFFIXES={JE_SUFFIX,DEL_SUFFIX};
  private boolean syncAtFileEnd=true;
  private EnvironmentImpl envImpl;
  private long maxFileSize;
  private File dbEnvHome;
  private boolean includeDeletedFiles=false;
  private boolean readOnly;
  private long currentFileNum;
  private long nextAvailableLsn;
  private long lastUsedLsn;
  private long prevOffset;
  private boolean forceNewFile;
  private long savedCurrentFileNum;
  private long savedNextAvailableLsn;
  private long savedLastUsedLsn;
  private long savedPrevOffset;
  private boolean savedForceNewFile;
  private LogEndFileDescriptor endOfLog;
  private Map perFileLastUsedLsn;
  /** 
 * Set up the file cache and initialize the file manager to point to the
 * beginning of the log.
 * @param configManager
 * @param dbEnvHomeenvironment home directory
 */
  public FileManager(  EnvironmentImpl envImpl,  File dbEnvHome,  boolean readOnly) throws DatabaseException {
    this.envImpl=envImpl;
    this.dbEnvHome=dbEnvHome;
    this.readOnly=readOnly;
    DbConfigManager configManager=envImpl.getConfigManager();
    maxFileSize=configManager.getLong(EnvironmentParams.LOG_FILE_MAX);
    this.hook456(configManager);
    this.hook467(readOnly);
    this.hook457(configManager);
    this.hook449(envImpl);
    if (!dbEnvHome.exists()) {
      throw new LogException("Environment home " + dbEnvHome + " doesn't exist");
    }
    currentFileNum=0L;
    nextAvailableLsn=DbLsn.makeLsn(currentFileNum,firstLogEntryOffset());
    lastUsedLsn=DbLsn.NULL_LSN;
    perFileLastUsedLsn=new HashMap();
    prevOffset=0L;
    endOfLog=new LogEndFileDescriptor();
    forceNewFile=false;
    saveLastPosition();
    String stopOnWriteProp=System.getProperty("je.debug.stopOnWrite");
    if (stopOnWriteProp != null) {
      stopOnWriteCount=Long.parseLong(stopOnWriteProp);
    }
    this.hook452(envImpl);
  }
  /** 
 * Set the file manager's "end of log".
 * @param nextAvailableLsnLSN to be used for the next log entry
 * @param lastUsedLsnlast LSN to have a valid entry, may be null
 * @param prevOffsetvalue to use for the prevOffset of the next entry. If the
 * beginning of the file, this is 0.
 */
  public void setLastPosition(  long nextAvailableLsn,  long lastUsedLsn,  long prevOffset){
    this.lastUsedLsn=lastUsedLsn;
    perFileLastUsedLsn.put(new Long(DbLsn.getFileNumber(lastUsedLsn)),new Long(lastUsedLsn));
    this.nextAvailableLsn=nextAvailableLsn;
    currentFileNum=DbLsn.getFileNumber(this.nextAvailableLsn);
    this.prevOffset=prevOffset;
    saveLastPosition();
  }
  void saveLastPosition(){
    savedNextAvailableLsn=nextAvailableLsn;
    savedLastUsedLsn=lastUsedLsn;
    savedPrevOffset=prevOffset;
    savedForceNewFile=forceNewFile;
    savedCurrentFileNum=currentFileNum;
  }
  void restoreLastPosition(){
    nextAvailableLsn=savedNextAvailableLsn;
    lastUsedLsn=savedLastUsedLsn;
    prevOffset=savedPrevOffset;
    forceNewFile=savedForceNewFile;
    currentFileNum=savedCurrentFileNum;
  }
  /** 
 * May be used to disable sync at file end to speed unit tests. Must only be
 * used for unit testing, since log corruption may result.
 */
  public void setSyncAtFileEnd(  boolean sync){
    syncAtFileEnd=sync;
  }
  /** 
 * public for cleaner.
 * @return the number of the first file in this environment.
 */
  public Long getFirstFileNum(){
    return getFileNum(true);
  }
  public boolean getReadOnly(){
    return readOnly;
  }
  /** 
 * @return the number of the last file in this environment.
 */
  public Long getLastFileNum(){
    return getFileNum(false);
  }
  public long getCurrentFileNum(){
    return currentFileNum;
  }
  public void setIncludeDeletedFiles(  boolean includeDeletedFiles){
    this.includeDeletedFiles=includeDeletedFiles;
  }
  /** 
 * Get all JE file numbers.
 * @return an array of all JE file numbers.
 */
  public Long[] getAllFileNumbers(){
    String[] names=listFiles(JE_SUFFIXES);
    Long[] nums=new Long[names.length];
    for (int i=0; i < nums.length; i+=1) {
      nums[i]=getNumFromName(names[i]);
    }
    return nums;
  }
  /** 
 * Get the next file number before/after currentFileNum.
 * @param currentFileNumthe file we're at right now. Note that it may not exist, if
 * it's been cleaned and renamed.
 * @param forwardif true, we want the next larger file, if false we want the
 * previous file
 * @return null if there is no following file, or if filenum doesn't exist
 */
  public Long getFollowingFileNum(  long currentFileNum,  boolean forward){
    String[] names=listFiles(JE_SUFFIXES);
    String searchName=getFileName(currentFileNum,JE_SUFFIX);
    int foundIdx=Arrays.binarySearch(names,searchName);
    boolean foundTarget=false;
    if (foundIdx >= 0) {
      if (forward) {
        foundIdx++;
      }
 else {
        foundIdx--;
      }
    }
 else {
      foundIdx=Math.abs(foundIdx + 1);
      if (!forward) {
        foundIdx--;
      }
    }
    if (forward && (foundIdx < names.length)) {
      foundTarget=true;
    }
 else     if (!forward && (foundIdx > -1)) {
      foundTarget=true;
    }
    if (foundTarget) {
      return getNumFromName(names[foundIdx]);
    }
 else {
      return null;
    }
  }
  /** 
 * @return true if there are any files at all.
 */
  public boolean filesExist(){
    String[] names=listFiles(JE_SUFFIXES);
    return (names.length != 0);
  }
  /** 
 * Get the first or last file number in the set of je files.
 * @param firstif true, get the first file, else get the last file
 * @return the file number or null if no files exist
 */
  private Long getFileNum(  boolean first){
    String[] names=listFiles(JE_SUFFIXES);
    if (names.length == 0) {
      return null;
    }
 else {
      int index=0;
      if (!first) {
        index=names.length - 1;
      }
      return getNumFromName(names[index]);
    }
  }
  /** 
 * Get the file number from a file name.
 * @param thefile name
 * @return the file number
 */
  private Long getNumFromName(  String fileName){
    String fileNumber=fileName.substring(0,fileName.indexOf("."));
    return new Long(Long.parseLong(fileNumber,16));
  }
  /** 
 * Find je files. Return names sorted in ascending fashion.
 * @param suffixwhich type of file we're looking for
 * @return array of file names
 */
  String[] listFiles(  String[] suffixes){
    String[] fileNames=dbEnvHome.list(new JEFileFilter(suffixes));
    Arrays.sort(fileNames);
    return fileNames;
  }
  /** 
 * Find je files, flavor for unit test support.
 * @param suffixwhich type of file we're looking for
 * @return array of file names
 */
  public static String[] listFiles(  File envDirFile,  String[] suffixes){
    String[] fileNames=envDirFile.list(new JEFileFilter(suffixes));
    Arrays.sort(fileNames);
    return fileNames;
  }
  /** 
 * @return the full file name and path for the nth je file.
 */
  String[] getFullFileNames(  long fileNum){
    if (includeDeletedFiles) {
      int nSuffixes=JE_AND_DEL_SUFFIXES.length;
      String[] ret=new String[nSuffixes];
      for (int i=0; i < nSuffixes; i++) {
        ret[i]=getFullFileName(getFileName(fileNum,JE_AND_DEL_SUFFIXES[i]));
      }
      return ret;
    }
 else {
      return new String[]{getFullFileName(getFileName(fileNum,JE_SUFFIX))};
    }
  }
  /** 
 * @return the full file name and path for the given file number and suffix.
 */
  public String getFullFileName(  long fileNum,  String suffix){
    return getFullFileName(getFileName(fileNum,suffix));
  }
  /** 
 * @return the full file name and path for this file name.
 */
  private String getFullFileName(  String fileName){
    return dbEnvHome + File.separator + fileName;
  }
  /** 
 * @return the file name for the nth file.
 */
  public static String getFileName(  long fileNum,  String suffix){
    return (HexFormatter.formatLong(fileNum).substring(10) + suffix);
  }
  /** 
 * Rename this file to NNNNNNNN.suffix. If that file already exists, try
 * NNNNNNNN.suffix.1, etc. Used for deleting files or moving corrupt files
 * aside.
 * @param fileNumthe file we want to move
 * @param newSuffixthe new file suffix
 */
  public void renameFile(  long fileNum,  String newSuffix) throws DatabaseException, IOException {
    int repeatNum=0;
    boolean renamed=false;
    while (!renamed) {
      String generation="";
      if (repeatNum > 0) {
        generation="." + repeatNum;
      }
      String newName=getFullFileName(getFileName(fileNum,newSuffix) + generation);
      File targetFile=new File(newName);
      if (targetFile.exists()) {
        repeatNum++;
      }
 else {
        String oldFileName=getFullFileNames(fileNum)[0];
        this.hook458(fileNum);
        File oldFile=new File(oldFileName);
        if (oldFile.renameTo(targetFile)) {
          renamed=true;
        }
 else {
          throw new LogException("Couldn't rename " + oldFileName + " to "+ newName);
        }
      }
    }
  }
  /** 
 * Delete log file NNNNNNNN.
 * @param fileNumthe file we want to move
 */
  public void deleteFile(  long fileNum) throws DatabaseException, IOException {
    String fileName=getFullFileNames(fileNum)[0];
    this.hook459(fileNum);
    File file=new File(fileName);
    boolean done=file.delete();
    if (!done) {
      throw new LogException("Couldn't delete " + file);
    }
  }
  /** 
 * Return a read only file handle that corresponds the this file number.
 * Retrieve it from the cache or open it anew and validate the file header.
 * This method takes a latch on this file, so that the file descriptor will
 * be held in the cache as long as it's in use. When the user is done with
 * the file, the latch must be released.
 * @param fileNumwhich file
 * @return the file handle for the existing or newly created file
 */
  FileHandle getFileHandle(  long fileNum) throws LogException, DatabaseException {
    try {
      Long fileId=new Long(fileNum);
      FileHandle fileHandle=null;
      this.hook460(fileNum,fileId,fileHandle);
      throw ReturnHack.returnObject;
    }
 catch (    ReturnObject r) {
      return (FileHandle)r.value;
    }
  }
  private FileHandle makeFileHandle(  long fileNum,  FileMode mode) throws DatabaseException {
    String[] fileNames=getFullFileNames(fileNum);
    RandomAccessFile newFile=null;
    String fileName=null;
    try {
      FileNotFoundException FNFE=null;
      for (int i=0; i < fileNames.length; i++) {
        fileName=fileNames[i];
        try {
          newFile=new RandomAccessFile(fileName,mode.getModeValue());
          break;
        }
 catch (        FileNotFoundException e) {
          if (FNFE == null) {
            FNFE=e;
          }
        }
      }
      if (newFile == null) {
        throw FNFE;
      }
      boolean oldHeaderVersion=false;
      if (newFile.length() == 0) {
        if (mode == FileMode.READWRITE_MODE) {
          long lastLsn=DbLsn.longToLsn((Long)perFileLastUsedLsn.remove(new Long(fileNum - 1)));
          long headerPrevOffset=0;
          if (lastLsn != DbLsn.NULL_LSN) {
            headerPrevOffset=DbLsn.getFileOffset(lastLsn);
          }
          FileHeader fileHeader=new FileHeader(fileNum,headerPrevOffset);
          writeFileHeader(newFile,fileName,fileHeader);
        }
      }
 else {
        oldHeaderVersion=readAndValidateFileHeader(newFile,fileName,fileNum);
      }
      return new FileHandle(newFile,fileName,envImpl,oldHeaderVersion);
    }
 catch (    FileNotFoundException e) {
      throw new LogFileNotFoundException("Couldn't open file " + fileName + ": "+ e.getMessage());
    }
catch (    DbChecksumException e) {
      closeFileInErrorCase(newFile);
      throw new DbChecksumException(envImpl,"Couldn't open file " + fileName,e);
    }
catch (    Throwable t) {
      closeFileInErrorCase(newFile);
      throw new DatabaseException("Couldn't open file " + fileName + ": "+ t,t);
    }
  }
  /** 
 * Close this file and eat any exceptions. Used in catch clauses.
 */
  private void closeFileInErrorCase(  RandomAccessFile file){
    try {
      if (file != null) {
        file.close();
      }
    }
 catch (    IOException e) {
    }
  }
  /** 
 * Read the given je log file and validate the header.
 * @throws DatabaseExceptionif the file header isn't valid
 * @return whether the file header has an old version number.
 */
  private boolean readAndValidateFileHeader(  RandomAccessFile file,  String fileName,  long fileNum) throws DatabaseException, IOException {
    LogManager logManager=envImpl.getLogManager();
    LogEntry headerEntry=logManager.getLogEntry(DbLsn.makeLsn(fileNum,0),file);
    FileHeader header=(FileHeader)headerEntry.getMainItem();
    return header.validate(fileName,fileNum);
  }
  /** 
 * Write a proper file header to the given file.
 */
  private void writeFileHeader(  RandomAccessFile file,  String fileName,  FileHeader header) throws DatabaseException, IOException {
    envImpl.checkIfInvalid();
    if (envImpl.mayNotWrite()) {
      return;
    }
    int headerSize=header.getLogSize();
    int entrySize=headerSize + LogManager.HEADER_BYTES;
    ByteBuffer headerBuf=envImpl.getLogManager().putIntoBuffer(header,headerSize,0,false,entrySize);
    if (++writeCount >= stopOnWriteCount) {
      Runtime.getRuntime().halt(0xff);
    }
    int bytesWritten;
    try {
      if (RUNRECOVERY_EXCEPTION_TESTING) {
        generateRunRecoveryException(file,headerBuf,0);
      }
      bytesWritten=writeToFile(file,headerBuf,0);
    }
 catch (    ClosedChannelException e) {
      throw new RunRecoveryException(envImpl,"Channel closed, may be due to thread interrupt",e);
    }
catch (    IOException e) {
      throw new RunRecoveryException(envImpl,"IOException caught: " + e);
    }
    if (bytesWritten != entrySize) {
      throw new LogException("File " + fileName + " was created with an incomplete header. Only "+ bytesWritten+ " bytes were written.");
    }
  }
  /** 
 * @return the prevOffset field stored in the file header.
 */
  long getFileHeaderPrevOffset(  long fileNum) throws IOException, DatabaseException {
    LogEntry headerEntry=envImpl.getLogManager().getLogEntry(DbLsn.makeLsn(fileNum,0));
    FileHeader header=(FileHeader)headerEntry.getMainItem();
    return header.getLastEntryInPrevFileOffset();
  }
  /** 
 * @return the file offset of the last LSN that was used. For constructing
 * the headers of log entries. If the last LSN that was used was in
 * a previous file, or this is the very first LSN of the whole
 * system, return 0.
 */
  long getPrevEntryOffset(){
    return prevOffset;
  }
  /** 
 * Increase the current log position by "size" bytes. Move the prevOffset
 * pointer along.
 * @param sizeis an unsigned int
 * @return true if we flipped to the next log file.
 */
  boolean bumpLsn(  long size){
    saveLastPosition();
    boolean flippedFiles=false;
    if (forceNewFile || (DbLsn.getFileOffset(nextAvailableLsn) + size) > maxFileSize) {
      forceNewFile=false;
      currentFileNum++;
      if (lastUsedLsn != DbLsn.NULL_LSN) {
        perFileLastUsedLsn.put(new Long(DbLsn.getFileNumber(lastUsedLsn)),new Long(lastUsedLsn));
      }
      prevOffset=0;
      lastUsedLsn=DbLsn.makeLsn(currentFileNum,firstLogEntryOffset());
      flippedFiles=true;
    }
 else {
      if (lastUsedLsn == DbLsn.NULL_LSN) {
        prevOffset=0;
      }
 else {
        prevOffset=DbLsn.getFileOffset(lastUsedLsn);
      }
      lastUsedLsn=nextAvailableLsn;
    }
    nextAvailableLsn=DbLsn.makeLsn(DbLsn.getFileNumber(lastUsedLsn),(DbLsn.getFileOffset(lastUsedLsn) + size));
    return flippedFiles;
  }
  /** 
 * Write out a log buffer to the file.
 * @param fullBufferbuffer to write
 */
  void writeLogBuffer(  LogBuffer fullBuffer) throws DatabaseException {
    envImpl.checkIfInvalid();
    if (envImpl.mayNotWrite()) {
      return;
    }
    long firstLsn=fullBuffer.getFirstLsn();
    if (firstLsn != DbLsn.NULL_LSN) {
      RandomAccessFile file=endOfLog.getWritableFile(DbLsn.getFileNumber(firstLsn));
      ByteBuffer data=fullBuffer.getDataBuffer();
      if (++writeCount >= stopOnWriteCount) {
        Runtime.getRuntime().halt(0xff);
      }
      try {
        this.hook465(fullBuffer,firstLsn,file);
        if (IO_EXCEPTION_TESTING) {
          throw new IOException("generated for testing");
        }
        if (RUNRECOVERY_EXCEPTION_TESTING) {
          generateRunRecoveryException(file,data,DbLsn.getFileOffset(firstLsn));
        }
        writeToFile(file,data,DbLsn.getFileOffset(firstLsn));
      }
 catch (      ClosedChannelException e) {
        throw new RunRecoveryException(envImpl,"File closed, may be due to thread interrupt",e);
      }
catch (      IOException IOE) {
        abortCommittedTxns(data);
        this.hook466(fullBuffer,firstLsn,file,data,IOE);
      }
      assert EnvironmentImpl.maybeForceYield();
    }
  }
  /** 
 * Write a buffer to a file at a given offset, using NIO if so configured.
 */
  private int writeToFile(  RandomAccessFile file,  ByteBuffer data,  long destOffset) throws IOException, DatabaseException {
    return new FileManager_writeToFile(this,file,data,destOffset).execute();
  }
  /** 
 * Read a buffer from a file at a given offset, using NIO if so configured.
 */
  void readFromFile(  RandomAccessFile file,  ByteBuffer readBuffer,  long offset) throws IOException {
    new FileManager_readFromFile(this,file,readBuffer,offset).execute();
  }
  private void abortCommittedTxns(  ByteBuffer data){
    final byte commitType=LogEntryType.LOG_TXN_COMMIT.getTypeNum();
    final byte abortType=LogEntryType.LOG_TXN_ABORT.getTypeNum();
    this.hook461(data);
    while (data.remaining() > 0) {
      int recStartPos=data.position();
      data.position(recStartPos + LogManager.HEADER_ENTRY_TYPE_OFFSET);
      int typePos=data.position();
      byte entryType=data.get();
      boolean recomputeChecksum=false;
      if (entryType == commitType) {
        data.position(typePos);
        data.put(abortType);
        recomputeChecksum=true;
      }
      byte version=data.get();
      data.position(data.position() + LogManager.PREV_BYTES);
      int itemSize=LogUtils.readInt(data);
      int itemDataStartPos=data.position();
      if (recomputeChecksum) {
        Checksum checksum=Adler32.makeChecksum();
        data.position(recStartPos);
        int nChecksumBytes=itemSize + (LogManager.HEADER_BYTES - LogManager.CHECKSUM_BYTES);
        byte[] checksumBytes=new byte[nChecksumBytes];
        System.arraycopy(data.array(),recStartPos + LogManager.CHECKSUM_BYTES,checksumBytes,0,nChecksumBytes);
        checksum.update(checksumBytes,0,nChecksumBytes);
        LogUtils.writeUnsignedInt(data,checksum.getValue());
      }
      data.position(itemDataStartPos + itemSize);
    }
    data.position(0);
  }
  /** 
 * FSync the end of the log.
 */
  void syncLogEnd() throws DatabaseException {
    try {
      endOfLog.force();
    }
 catch (    IOException e) {
      throw new DatabaseException(e);
    }
  }
  /** 
 * Sync the end of the log, close off this log file. Should only be called
 * under the log write latch.
 */
  void syncLogEndAndFinishFile() throws DatabaseException, IOException {
    if (syncAtFileEnd) {
      syncLogEnd();
    }
    endOfLog.close();
  }
  /** 
 * Close all file handles and empty the cache.
 */
  public void clear() throws IOException, DatabaseException {
    endOfLog.close();
  }
  /** 
 * Clear the file lock.
 */
  public void close() throws IOException, DatabaseException {
  }
  /** 
 * Ensure that if the environment home dir is on readonly media or in a
 * readonly directory that the environment has been opened for readonly
 * access.
 * @return true if the environment home dir is readonly.
 */
  private boolean checkEnvHomePermissions(  boolean readOnly) throws DatabaseException {
    boolean envDirIsReadOnly=!dbEnvHome.canWrite();
    if (envDirIsReadOnly && !readOnly) {
      throw new DatabaseException("The Environment directory " + dbEnvHome + " is not writable, but the "+ "Environment was opened for read-write access.");
    }
    return envDirIsReadOnly;
  }
  /** 
 * Truncate a log at this position. Used by recovery to a timestamp
 * utilities and by recovery to set the end-of-log position.
 * <p>
 * This method forces a new log file to be written next, if the last file
 * (the file truncated to) has an old version in its header. This ensures
 * that when the log is opened by an old version of JE, a version
 * incompatibility will be detected. [#11243]
 * </p>
 */
  public void truncateLog(  long fileNum,  long offset) throws IOException, DatabaseException {
    FileHandle handle=makeFileHandle(fileNum,FileMode.READWRITE_MODE);
    RandomAccessFile file=handle.getFile();
    try {
      file.getChannel().truncate(offset);
    }
  finally {
      file.close();
    }
    if (handle.isOldHeaderVersion()) {
      forceNewFile=true;
    }
  }
  /** 
 * Set the flag that causes a new file to be written before the next write.
 */
  void forceNewLogFile(){
    forceNewFile=true;
  }
  /** 
 * @return the size in bytes of the file header log entry.
 */
  public static int firstLogEntryOffset(){
    return FileHeader.entrySize() + LogManager.HEADER_BYTES;
  }
  /** 
 * Return the next available LSN in the log. Note that this is
 * unsynchronized, so is only valid as an approximation of log size.
 */
  public long getNextLsn(){
    return nextAvailableLsn;
  }
  /** 
 * Return the last allocated LSN in the log. Note that this is
 * unsynchronized, so if it is called outside the log write latch it is only
 * valid as an approximation of log size.
 */
  public long getLastUsedLsn(){
    return lastUsedLsn;
  }
  /** 
 * The LogEndFileDescriptor is used to write and fsync the end of the log.
 * Because the JE log is append only, there is only one logical R/W file
 * descriptor for the whole environment. This class actually implements two
 * RandomAccessFile instances, one for writing and one for fsyncing, so the
 * two types of operations don't block each other.
 * The write file descriptor is considered the master. Manipulation of this
 * class is done under the log write latch. Here's an explanation of why the
 * log write latch is sufficient to safeguard all operations.
 * There are two types of callers who may use this file descriptor: the
 * thread that is currently writing to the end of the log and any threads
 * that are fsyncing on behalf of the FSyncManager.
 * The writing thread appends data to the file and fsyncs the file when we
 * flip over to a new log file. The file is only instantiated at the point
 * that it must do so -- which is either when the first fsync is required by
 * JE or when the log file is full and we flip files. Therefore, the writing
 * thread has two actions that change this descriptor -- we initialize the
 * file descriptor for the given log file at the first write to the file,
 * and we close the file descriptor when the log file is full. Therefore is
 * a period when there is no log descriptor -- when we have not yet written
 * a log buffer into a given log file.
 * The fsyncing threads ask for the log end file descriptor asynchronously,
 * but will never modify it. These threads may arrive at the point when the
 * file descriptor is null, and therefore skip their fysnc, but that is fine
 * because it means a writing thread already flipped that target file and
 * has moved on to the next file.
 * Time Activity 10 thread 1 writes log entry A into file 0x0, issues fsync
 * outside of log write latch, yields the processor 20 thread 2 writes log
 * entry B, piggybacks off thread 1 30 thread 3 writes log entry C, but no
 * room left in that file, so it flips the log, and fsyncs file 0x0, all
 * under the log write latch. It nulls out endOfLogRWFile, moves onto file
 * 0x1, but doesn't create the file yet. 40 thread 1 finally comes along,
 * but endOfLogRWFile is null-- no need to fsync in that case, 0x0 got
 * fsynced.
 */
class LogEndFileDescriptor {
    private RandomAccessFile endOfLogRWFile=null;
    private RandomAccessFile endOfLogSyncFile=null;
    /** 
 * getWritableFile must be called under the log write latch.
 */
    RandomAccessFile getWritableFile(    long fileNumber) throws RunRecoveryException {
      try {
        if (endOfLogRWFile == null) {
          endOfLogRWFile=makeFileHandle(fileNumber,FileMode.READWRITE_MODE).getFile();
          endOfLogSyncFile=makeFileHandle(fileNumber,FileMode.READWRITE_MODE).getFile();
        }
        return endOfLogRWFile;
      }
 catch (      Exception e) {
        throw new RunRecoveryException(envImpl,e);
      }
    }
    /** 
 * FSync the log file that makes up the end of the log.
 */
    void force() throws DatabaseException, IOException {
      RandomAccessFile file=endOfLogSyncFile;
      if (file != null) {
        FileChannel channel=file.getChannel();
        try {
          channel.force(false);
        }
 catch (        ClosedChannelException e) {
          throw new RunRecoveryException(envImpl,"Channel closed, may be due to thread interrupt",e);
        }
        assert EnvironmentImpl.maybeForceYield();
      }
    }
    /** 
 * Close the end of the log file descriptor. Use atomic assignment to
 * ensure that we won't force and close on the same descriptor.
 */
    void close() throws IOException {
      IOException firstException=null;
      if (endOfLogRWFile != null) {
        RandomAccessFile file=endOfLogRWFile;
        endOfLogRWFile=null;
        try {
          file.close();
        }
 catch (        IOException e) {
          firstException=e;
        }
      }
      if (endOfLogSyncFile != null) {
        RandomAccessFile file=endOfLogSyncFile;
        endOfLogSyncFile=null;
        file.close();
      }
      if (firstException != null) {
        throw firstException;
      }
    }
  }
  static boolean RUNRECOVERY_EXCEPTION_TESTING=false;
  private static final int RUNRECOVERY_EXCEPTION_MAX=100;
  private int runRecoveryExceptionCounter=0;
  private boolean runRecoveryExceptionThrown=false;
  private Random runRecoveryExceptionRandom=null;
  private void generateRunRecoveryException(  RandomAccessFile file,  ByteBuffer data,  long destOffset) throws DatabaseException, IOException {
    if (runRecoveryExceptionThrown) {
      try {
        throw new Exception("Write after RunRecoveryException");
      }
 catch (      Exception e) {
        e.printStackTrace();
      }
    }
    runRecoveryExceptionCounter+=1;
    if (runRecoveryExceptionCounter >= RUNRECOVERY_EXCEPTION_MAX) {
      runRecoveryExceptionCounter=0;
    }
    if (runRecoveryExceptionRandom == null) {
      runRecoveryExceptionRandom=new Random(System.currentTimeMillis());
    }
    if (runRecoveryExceptionCounter == runRecoveryExceptionRandom.nextInt(RUNRECOVERY_EXCEPTION_MAX)) {
      int len=runRecoveryExceptionRandom.nextInt(data.remaining());
      if (len > 0) {
        byte[] a=new byte[len];
        data.get(a,0,len);
        ByteBuffer buf=ByteBuffer.wrap(a);
        writeToFile(file,buf,destOffset);
      }
      runRecoveryExceptionThrown=true;
      throw new RunRecoveryException(envImpl,"Randomly generated for testing");
    }
  }
@MethodObject static class FileManager_writeToFile {
    FileManager_writeToFile(    FileManager _this,    RandomAccessFile file,    ByteBuffer data,    long destOffset){
      this._this=_this;
      this.file=file;
      this.data=data;
      this.destOffset=destOffset;
    }
    int execute() throws IOException, DatabaseException {
      totalBytesWritten=0;
      this.hook455();
      this.hook445();
      return totalBytesWritten;
    }
    protected FileManager _this;
    protected RandomAccessFile file;
    protected ByteBuffer data;
    protected long destOffset;
    protected int totalBytesWritten;
    protected FileChannel channel;
    protected ByteBuffer useData;
    protected int origLimit;
    protected int bytesWritten;
    protected int pos;
    protected int size;
    protected void hook445() throws IOException, DatabaseException {
    }
    protected void hook455() throws IOException, DatabaseException {
    }
  }
@MethodObject static class FileManager_readFromFile {
    FileManager_readFromFile(    FileManager _this,    RandomAccessFile file,    ByteBuffer readBuffer,    long offset){
      this._this=_this;
      this.file=file;
      this.readBuffer=readBuffer;
      this.offset=offset;
    }
    void execute() throws IOException {
      this.hook446();
    }
    protected FileManager _this;
    protected RandomAccessFile file;
    protected ByteBuffer readBuffer;
    protected long offset;
    protected FileChannel channel;
    protected int readLength;
    protected long currentPosition;
    protected int bytesRead1;
    protected int pos;
    protected int size;
    protected int bytesRead2;
    protected void hook446() throws IOException {
    }
  }
  protected void hook449(  EnvironmentImpl envImpl) throws DatabaseException {
  }
  protected FileHandle hook450(  long fileNum,  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
    fileHandle=this.hook462(fileNum,fileId,fileHandle);
    return fileHandle;
  }
  protected void hook452(  EnvironmentImpl envImpl) throws DatabaseException {
  }
  protected void hook453(  FileHandle fileHandle) throws LogException, DatabaseException {
  }
  protected void hook454(  FileHandle fileHandle) throws LogException, DatabaseException {
  }
  protected void hook456(  DbConfigManager configManager) throws DatabaseException {
  }
  protected void hook457(  DbConfigManager configManager) throws DatabaseException {
  }
  protected void hook458(  long fileNum) throws DatabaseException, IOException {
  }
  protected void hook459(  long fileNum) throws DatabaseException, IOException {
  }
  protected void hook460(  long fileNum,  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
    fileHandle=this.hook463(fileNum,fileId,fileHandle);
    this.hook453(fileHandle);
    if (fileHandle.getFile() == null) {
      this.hook454(fileHandle);
    }
 else {
      throw new ReturnObject(fileHandle);
    }
  }
  protected void hook461(  ByteBuffer data){
  }
  protected FileHandle hook462(  long fileNum,  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
    fileHandle=makeFileHandle(fileNum,FileMode.READ_MODE);
    this.hook464(fileId,fileHandle);
    return fileHandle;
  }
  protected FileHandle hook463(  long fileNum,  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
    fileHandle=this.hook450(fileNum,fileId,fileHandle);
    return fileHandle;
  }
  protected void hook464(  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
  }
  protected void hook465(  LogBuffer fullBuffer,  long firstLsn,  RandomAccessFile file) throws DatabaseException, ClosedChannelException, IOException {
  }
  protected void hook466(  LogBuffer fullBuffer,  long firstLsn,  RandomAccessFile file,  ByteBuffer data,  IOException IOE) throws DatabaseException {
    throw new DatabaseException(IOE);
  }
  protected void hook467(  boolean readOnly) throws DatabaseException {
  }
}
