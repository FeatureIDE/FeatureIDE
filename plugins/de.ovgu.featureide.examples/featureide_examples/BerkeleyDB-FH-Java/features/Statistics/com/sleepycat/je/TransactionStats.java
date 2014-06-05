package com.sleepycat.je;
import java.io.Serializable;
import java.util.Date;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class TransactionStats implements Serializable {
  /** 
 * The time the last completed checkpoint finished (as the number
 * of seconds since the Epoch, returned by the IEEE/ANSI Std
 * 1003.1 (POSIX) time interface).
 */
  private long lastCheckpointTime;
  /** 
 * The last transaction ID allocated.
 */
  private long lastTxnId;
  /** 
 * The number of transactions that are currently active.
 */
  private int nActive;
  /** 
 * The number of transactions that have begun.
 */
  private int nBegins;
  /** 
 * The number of transactions that have aborted.
 */
  private int nAborts;
  /** 
 * The number of transactions that have committed.
 */
  private int nCommits;
  /** 
 * The number of XA transactions that have aborted.
 */
  private int nXAAborts;
  /** 
 * The number of XA transactions that have been prepared.
 */
  private int nXAPrepares;
  /** 
 * The number of XA transactions that have committed.
 */
  private int nXACommits;
  /** 
 * The array of active transactions. Each element of the array is
 * an object of type TransactionStats.Active.
 */
  private Active activeTxns[];
  /** 
 * Internal use only.
 */
  public TransactionStats(){
  }
  /** 
 * The Active class represents an active transaction.
 */
public static class Active implements Serializable {
    /** 
 * The transaction ID of the transaction.
 */
    private long txnId;
    /** 
 * The transaction ID of the parent transaction (or 0, if no parent).
 */
    private long parentId;
    /** 
 * The transaction name, including the thread name if available.
 */
    private String name;
    /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
    public long getId(){
      return txnId;
    }
    /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
    public long getParentId(){
      return parentId;
    }
    /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
    public String getName(){
      return name;
    }
    /** 
 * Internal use only.
 */
    public Active(    String name,    long txnId,    long parentId){
      this.name=name;
      this.txnId=txnId;
      this.parentId=parentId;
    }
    public String toString(){
      return "txnId = " + txnId + " txnName = "+ name;
    }
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public Active[] getActiveTxns(){
    return activeTxns;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getLastCheckpointTime(){
    return lastCheckpointTime;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getLastTxnId(){
    return lastTxnId;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNAborts(){
    return nAborts;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNXAAborts(){
    return nXAAborts;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNXAPrepares(){
    return nXAPrepares;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNActive(){
    return nActive;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNBegins(){
    return nBegins;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNCommits(){
    return nCommits;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNXACommits(){
    return nXACommits;
  }
  /** 
 * Internal use only.
 */
  public void setActiveTxns(  Active[] actives){
    activeTxns=actives;
  }
  /** 
 * Internal use only.
 */
  public void setLastCheckpointTime(  long l){
    lastCheckpointTime=l;
  }
  /** 
 * Internal use only.
 */
  public void setLastTxnId(  long val){
    lastTxnId=val;
  }
  /** 
 * Internal use only.
 */
  public void setNAborts(  int val){
    nAborts=val;
  }
  /** 
 * Internal use only.
 */
  public void setNXAAborts(  int val){
    nXAAborts=val;
  }
  /** 
 * Internal use only.
 */
  public void setNActive(  int val){
    nActive=val;
  }
  /** 
 * Internal use only.
 */
  public void setNBegins(  int val){
    nBegins=val;
  }
  /** 
 * Internal use only.
 */
  public void setNCommits(  int val){
    nCommits=val;
  }
  /** 
 * Internal use only.
 */
  public void setNXACommits(  int val){
    nXACommits=val;
  }
  /** 
 * Internal use only.
 */
  public void setNXAPrepares(  int val){
    nXAPrepares=val;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public String toString(){
    StringBuffer sb=new StringBuffer();
    sb.append("nBegins=").append(nBegins).append('\n');
    sb.append("nAborts=").append(nAborts).append('\n');
    sb.append("nCommits=").append(nCommits).append('\n');
    sb.append("nXAPrepares=").append(nXAPrepares).append('\n');
    sb.append("nXAAborts=").append(nXAAborts).append('\n');
    sb.append("nXACommits=").append(nXACommits).append('\n');
    sb.append("nActive=").append(nActive).append('\n');
    sb.append("activeTxns=[");
    if (activeTxns != null) {
      for (int i=0; i < activeTxns.length; i+=1) {
        sb.append("  ").append(activeTxns[i]).append('\n');
      }
    }
    sb.append("]\n");
    sb.append("lastTxnId=").append(lastTxnId).append('\n');
    sb.append("lastCheckpointTime=").append(new Date(lastCheckpointTime)).append('\n');
    return sb.toString();
  }
}
