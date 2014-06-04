package com.sleepycat.je;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated via
 * the doc templates in the doc_src directory.
 */
public class SequenceStats {
  private int nGets;
  private int nCachedGets;
  private long current;
  private long value;
  private long lastValue;
  private long min;
  private long max;
  private int cacheSize;
  SequenceStats(  int nGets,  int nCachedGets,  long current,  long value,  long lastValue,  long min,  long max,  int cacheSize){
    this.nGets=nGets;
    this.nCachedGets=nCachedGets;
    this.current=current;
    this.value=value;
    this.lastValue=lastValue;
    this.min=min;
    this.max=max;
    this.cacheSize=cacheSize;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNGets(){
    return nGets;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNCachedGets(){
    return nCachedGets;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getCurrent(){
    return current;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getValue(){
    return value;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getLastValue(){
    return lastValue;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getMin(){
    return min;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getMax(){
    return max;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getCacheSize(){
    return cacheSize;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public String toString(){
    return "nGets=" + nGets + "\nnCachedGets="+ nCachedGets+ "\ncurrent="+ current+ "\nvalue="+ value+ "\nlastValue="+ lastValue+ "\nmin="+ min+ "\nmax="+ max+ "\ncacheSize="+ cacheSize;
  }
}
