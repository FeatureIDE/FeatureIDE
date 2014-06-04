package com.sleepycat.je.incomp;
import com.sleepycat.je.EnvironmentStats;
import com.sleepycat.je.StatsConfig;
public class INCompressor {
  private int splitBins=0;
  private int dbClosedBins=0;
  private int cursorsBins=0;
  private int nonEmptyBins=0;
  private int processedBins=0;
  private int splitBinsThisRun=0;
  private int dbClosedBinsThisRun=0;
  private int cursorsBinsThisRun=0;
  private int nonEmptyBinsThisRun=0;
  private int processedBinsThisRun=0;
  private int lazyProcessed=0;
  private int lazyEmpty=0;
  private int lazySplit=0;
  private int wokenUp=0;
  /** 
 * Return stats
 */
  public void loadStats(  StatsConfig config,  EnvironmentStats stat) throws DatabaseException {
    stat.setSplitBins(splitBins);
    stat.setDbClosedBins(dbClosedBins);
    stat.setCursorsBins(cursorsBins);
    stat.setNonEmptyBins(nonEmptyBins);
    stat.setProcessedBins(processedBins);
    stat.setInCompQueueSize(getBinRefQueueSize());
    if (DEBUG) {
      System.out.println("lazyProcessed = " + lazyProcessed);
      System.out.println("lazyEmpty = " + lazyEmpty);
      System.out.println("lazySplit = " + lazySplit);
      System.out.println("wokenUp=" + wokenUp);
    }
    if (config.getClear()) {
      splitBins=0;
      dbClosedBins=0;
      cursorsBins=0;
      nonEmptyBins=0;
      processedBins=0;
      lazyProcessed=0;
      lazyEmpty=0;
      lazySplit=0;
      wokenUp=0;
    }
  }
  /** 
 * Reset per-run counters.
 */
  private void resetPerRunCounters(){
    splitBinsThisRun=0;
    dbClosedBinsThisRun=0;
    cursorsBinsThisRun=0;
    nonEmptyBinsThisRun=0;
    processedBinsThisRun=0;
  }
  private void accumulatePerRunCounters(){
    splitBins+=splitBinsThisRun;
    dbClosedBins+=dbClosedBinsThisRun;
    cursorsBins+=cursorsBinsThisRun;
    nonEmptyBins+=nonEmptyBinsThisRun;
    processedBins+=processedBinsThisRun;
  }
  protected void hook403() throws DatabaseException {
    wokenUp++;
    original();
  }
  protected void hook404() throws DatabaseException {
    resetPerRunCounters();
    original();
  }
  protected void hook405() throws DatabaseException {
    accumulatePerRunCounters();
    original();
  }
  protected void hook406() throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    processedBinsThisRun++;
    original();
  }
  protected void hook407() throws DatabaseException {
    nonEmptyBinsThisRun++;
    original();
  }
  protected void hook408() throws DatabaseException {
    cursorsBinsThisRun++;
    original();
  }
  protected void hook409() throws DatabaseException {
    lazyProcessed++;
    original();
  }
  protected void hook410() throws DatabaseException {
    lazySplit++;
    original();
  }
  protected void hook411() throws DatabaseException {
    lazyEmpty++;
    original();
  }
  protected void hook412() throws DatabaseException {
    dbClosedBinsThisRun++;
    original();
  }
  protected void hook413() throws DatabaseException {
    splitBinsThisRun++;
    original();
  }
  protected void hook414() throws DatabaseException {
    cursorsBinsThisRun++;
    original();
  }
}
