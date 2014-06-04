package com.sleepycat.je.cleaner;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.log.LogReadable;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LogWritable;
import de.ovgu.cide.jakutil.*;
public class FileSummary implements LogWritable, LogReadable {
  public int totalCount;
  public int totalSize;
  public int totalINCount;
  public int totalINSize;
  public int totalLNCount;
  public int totalLNSize;
  public int obsoleteINCount;
  public int obsoleteLNCount;
  /** 
 * Creates an empty summary.
 */
  public FileSummary(){
  }
  /** 
 * Returns whether this summary contains any non-zero totals.
 */
  public boolean isEmpty(){
    return totalCount == 0 && totalSize == 0 && obsoleteINCount == 0 && obsoleteLNCount == 0;
  }
  /** 
 * Returns the approximate byte size of all obsolete LN entries.
 */
  public int getObsoleteLNSize(){
    if (totalLNCount == 0) {
      return 0;
    }
    long totalSize=totalLNSize;
    totalSize<<=8;
    long avgSizePerLN=totalSize / totalLNCount;
    return (int)((obsoleteLNCount * avgSizePerLN) >> 8);
  }
  /** 
 * Returns the approximate byte size of all obsolete IN entries.
 */
  public int getObsoleteINSize(){
    if (totalINCount == 0) {
      return 0;
    }
    long totalSize=totalINSize;
    totalSize<<=8;
    long avgSizePerIN=totalSize / totalINCount;
    return (int)((obsoleteINCount * avgSizePerIN) >> 8);
  }
  /** 
 * Returns an estimate of the total bytes that are obsolete.
 */
  public int getObsoleteSize() throws DatabaseException {
    if (totalSize > 0) {
      int leftoverSize=totalSize - (totalINSize + totalLNSize);
      int obsoleteSize=getObsoleteLNSize() + getObsoleteINSize() + leftoverSize;
      if (obsoleteSize > totalSize) {
        obsoleteSize=totalSize;
      }
      return obsoleteSize;
    }
 else {
      return 0;
    }
  }
  /** 
 * Returns the total number of entries counted.  This value is guaranted
 * to increase whenever the tracking information about a file changes.  It
 * is used a key discriminator for FileSummaryLN records.
 */
  public int getEntriesCounted(){
    return totalCount + obsoleteLNCount + obsoleteINCount;
  }
  /** 
 * Returns the number of non-obsolete LN and IN entries.
 */
  public int getNonObsoleteCount(){
    return totalLNCount + totalINCount - obsoleteLNCount - obsoleteINCount;
  }
  /** 
 * Reset all totals to zero.
 */
  public void reset(){
    totalCount=0;
    totalSize=0;
    totalINCount=0;
    totalINSize=0;
    totalLNCount=0;
    totalLNSize=0;
    obsoleteINCount=0;
    obsoleteLNCount=0;
  }
  /** 
 * Add the totals of the given summary object to the totals of this object.
 */
  public void add(  FileSummary o){
    totalCount+=o.totalCount;
    totalSize+=o.totalSize;
    totalINCount+=o.totalINCount;
    totalINSize+=o.totalINSize;
    totalLNCount+=o.totalLNCount;
    totalLNSize+=o.totalLNSize;
    obsoleteINCount+=o.obsoleteINCount;
    obsoleteLNCount+=o.obsoleteLNCount;
  }
  /** 
 * @see LogWritable#getLogSize
 */
  public int getLogSize(){
    return 8 * LogUtils.getIntLogSize();
  }
  /** 
 * @see LogWritable#writeToLog
 */
  public void writeToLog(  ByteBuffer buf){
    LogUtils.writeInt(buf,totalCount);
    LogUtils.writeInt(buf,totalSize);
    LogUtils.writeInt(buf,totalINCount);
    LogUtils.writeInt(buf,totalINSize);
    LogUtils.writeInt(buf,totalLNCount);
    LogUtils.writeInt(buf,totalLNSize);
    LogUtils.writeInt(buf,obsoleteINCount);
    LogUtils.writeInt(buf,obsoleteLNCount);
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer buf,  byte entryTypeVersion){
    totalCount=LogUtils.readInt(buf);
    totalSize=LogUtils.readInt(buf);
    totalINCount=LogUtils.readInt(buf);
    totalINSize=LogUtils.readInt(buf);
    totalLNCount=LogUtils.readInt(buf);
    totalLNSize=LogUtils.readInt(buf);
    obsoleteINCount=LogUtils.readInt(buf);
    if (obsoleteINCount == -1) {
      obsoleteINCount=totalINCount;
    }
    obsoleteLNCount=LogUtils.readInt(buf);
  }
  /** 
 * @see LogReadable#dumpLog
 */
  public void dumpLog(  StringBuffer buf,  boolean verbose){
    buf.append("<summary totalCount=\"");
    buf.append(totalCount);
    buf.append("\" totalSize=\"");
    buf.append(totalSize);
    buf.append("\" totalINCount=\"");
    buf.append(totalINCount);
    buf.append("\" totalINSize=\"");
    buf.append(totalINSize);
    buf.append("\" totalLNCount=\"");
    buf.append(totalLNCount);
    buf.append("\" totalLNSize=\"");
    buf.append(totalLNSize);
    buf.append("\" obsoleteINCount=\"");
    buf.append(obsoleteINCount);
    buf.append("\" obsoleteLNCount=\"");
    buf.append(obsoleteLNCount);
    buf.append("\"/>");
  }
  /** 
 * Never called.
 * @see LogReadable#getTransactionId
 */
  public long getTransactionId(){
    return -1;
  }
  /** 
 * Never called.
 * @see LogReadable#logEntryIsTransactional
 */
  public boolean logEntryIsTransactional(){
    return false;
  }
  public String toString(){
    StringBuffer buf=new StringBuffer();
    dumpLog(buf,true);
    return buf.toString();
  }
}
