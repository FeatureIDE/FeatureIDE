package com.sleepycat.je.dbi;
class PreloadProcessor {
  private PreloadStats stats;
  protected void hook353(  PreloadStats stats){
    this.stats=stats;
    original(stats);
  }
  protected void hook354(  LogEntryType childType){
    if (childType.equals(LogEntryType.LOG_DUPCOUNTLN_TRANSACTIONAL) || childType.equals(LogEntryType.LOG_DUPCOUNTLN)) {
      stats.nDupCountLNsLoaded++;
    }
 else     if (childType.equals(LogEntryType.LOG_LN_TRANSACTIONAL) || childType.equals(LogEntryType.LOG_LN)) {
      stats.nLNsLoaded++;
    }
 else     if (childType.equals(LogEntryType.LOG_DBIN)) {
      stats.nDBINsLoaded++;
    }
 else     if (childType.equals(LogEntryType.LOG_BIN)) {
      stats.nBINsLoaded++;
    }
 else     if (childType.equals(LogEntryType.LOG_DIN)) {
      stats.nDINsLoaded++;
    }
 else     if (childType.equals(LogEntryType.LOG_IN)) {
      stats.nINsLoaded++;
    }
    original(childType);
  }
}
