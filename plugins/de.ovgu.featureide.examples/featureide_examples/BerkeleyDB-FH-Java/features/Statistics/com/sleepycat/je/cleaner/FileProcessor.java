package com.sleepycat.je.cleaner;
class FileProcessor {
  private int nINsObsoleteThisRun=0;
  private int nINsCleanedThisRun=0;
  private int nINsDeadThisRun=0;
  private int nINsMigratedThisRun=0;
  private int nLNsObsoleteThisRun=0;
  private int nLNsCleanedThisRun=0;
  private int nLNsDeadThisRun=0;
  private int nLNsLockedThisRun=0;
  private int nLNsMigratedThisRun=0;
  private int nLNsMarkedThisRun=0;
  private int nLNQueueHitsThisRun=0;
  private int nEntriesReadThisRun;
  private long nRepeatIteratorReadsThisRun;
  /** 
 * Reset per-run counters.
 */
  private void resetPerRunCounters(){
    nINsObsoleteThisRun=0;
    nINsCleanedThisRun=0;
    nINsDeadThisRun=0;
    nINsMigratedThisRun=0;
    nLNsObsoleteThisRun=0;
    nLNsCleanedThisRun=0;
    nLNsDeadThisRun=0;
    nLNsMigratedThisRun=0;
    nLNsMarkedThisRun=0;
    nLNQueueHitsThisRun=0;
    nLNsLockedThisRun=0;
    nEntriesReadThisRun=0;
    nRepeatIteratorReadsThisRun=0;
  }
  /** 
 * Add per-run counters to total counters.
 */
  private void accumulatePerRunCounters(){
    cleaner.nINsObsolete+=nINsObsoleteThisRun;
    cleaner.nINsCleaned+=nINsCleanedThisRun;
    cleaner.nINsDead+=nINsDeadThisRun;
    cleaner.nINsMigrated+=nINsMigratedThisRun;
    cleaner.nLNsObsolete+=nLNsObsoleteThisRun;
    cleaner.nLNsCleaned+=nLNsCleanedThisRun;
    cleaner.nLNsDead+=nLNsDeadThisRun;
    cleaner.nLNsMigrated+=nLNsMigratedThisRun;
    cleaner.nLNsMarked+=nLNsMarkedThisRun;
    cleaner.nLNQueueHits+=nLNQueueHitsThisRun;
    cleaner.nLNsLocked+=nLNsLockedThisRun;
    cleaner.nRepeatIteratorReads+=nRepeatIteratorReadsThisRun;
  }
  protected void hook138() throws DatabaseException {
    resetPerRunCounters();
    original();
  }
  protected String hook139(  String traceMsg) throws DatabaseException, IOException {
    traceMsg+=" begins backlog=" + cleaner.nBacklogFiles;
    return original(traceMsg);
  }
  protected void hook140() throws DatabaseException, IOException {
    accumulatePerRunCounters();
    original();
  }
  protected String hook141(  String traceMsg) throws DatabaseException {
    traceMsg+=" nEntriesRead=" + nEntriesReadThisRun + " nINsObsolete="+ nINsObsoleteThisRun+ " nINsCleaned="+ nINsCleanedThisRun+ " nINsDead="+ nINsDeadThisRun+ " nINsMigrated="+ nINsMigratedThisRun+ " nLNsObsolete="+ nLNsObsoleteThisRun+ " nLNsCleaned="+ nLNsCleanedThisRun+ " nLNsDead="+ nLNsDeadThisRun+ " nLNsMigrated="+ nLNsMigratedThisRun+ " nLNsMarked="+ nLNsMarkedThisRun+ " nLNQueueHits="+ nLNQueueHitsThisRun+ " nLNsLocked="+ nLNsLockedThisRun;
    return original(traceMsg);
  }
  protected void hook142() throws DatabaseException {
    nLNsLockedThisRun++;
    original();
  }
  protected void hook143() throws DatabaseException {
    nLNsDeadThisRun++;
    original();
  }
  protected void hook144() throws DatabaseException {
    nLNsMarkedThisRun++;
    original();
  }
  protected void hook125(  IN inClone,  DatabaseImpl db,  long lsn,  boolean obsolete,  boolean dirtied,  boolean completed) throws DatabaseException {
    nINsCleanedThisRun++;
    original(inClone,db,lsn,obsolete,dirtied,completed);
  }
  protected void hook151() throws DatabaseException {
    nINsDeadThisRun++;
    original();
  }
  protected void hook152() throws DatabaseException {
    nINsDeadThisRun++;
    original();
  }
  protected void hook153() throws DatabaseException {
    nINsMigratedThisRun++;
    original();
  }
@MethodObject static class FileProcessor_processLN {
    void execute() throws DatabaseException {
      _this.nLNsCleanedThisRun++;
      original();
    }
    protected void hook148() throws DatabaseException {
      _this.nLNsDeadThisRun++;
      original();
    }
    protected void hook149() throws DatabaseException {
      _this.nLNsDeadThisRun++;
      original();
    }
    protected void hook150() throws DatabaseException {
      _this.nLNsDeadThisRun++;
      original();
    }
  }
@MethodObject static class FileProcessor_processFile {
    protected void hook145() throws DatabaseException, IOException {
      _this.nEntriesReadThisRun=reader.getNumRead();
      _this.nRepeatIteratorReadsThisRun=reader.getNRepeatIteratorReads();
      original();
    }
    protected void hook146() throws DatabaseException, IOException {
      _this.cleaner.nEntriesRead+=1;
      original();
    }
    protected void hook147() throws DatabaseException, IOException {
      if (isLN) {
        _this.nLNsObsoleteThisRun++;
      }
 else       if (isIN) {
        _this.nINsObsoleteThisRun++;
      }
      original();
    }
  }
}
