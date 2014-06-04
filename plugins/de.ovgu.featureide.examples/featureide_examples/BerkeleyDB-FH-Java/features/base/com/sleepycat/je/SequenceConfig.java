package com.sleepycat.je;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated via
 * the doc templates in the doc_src directory.
 */
public class SequenceConfig {
  public static final SequenceConfig DEFAULT=new SequenceConfig();
  private int cacheSize=0;
  private long rangeMin=Long.MIN_VALUE;
  private long rangeMax=Long.MAX_VALUE;
  private long initialValue=0L;
  private boolean allowCreate;
  private boolean decrement;
  private boolean exclusiveCreate;
  private boolean autoCommitNoSync;
  private boolean wrap;
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public SequenceConfig(){
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setAllowCreate(  boolean allowCreate){
    this.allowCreate=allowCreate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getAllowCreate(){
    return allowCreate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setCacheSize(  int cacheSize){
    this.cacheSize=cacheSize;
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
  public void setDecrement(  boolean decrement){
    this.decrement=decrement;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getDecrement(){
    return decrement;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setExclusiveCreate(  boolean exclusiveCreate){
    this.exclusiveCreate=exclusiveCreate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getExclusiveCreate(){
    return exclusiveCreate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setInitialValue(  long initialValue){
    this.initialValue=initialValue;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getInitialValue(){
    return initialValue;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setAutoCommitNoSync(  boolean autoCommitNoSync){
    this.autoCommitNoSync=autoCommitNoSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getAutoCommitNoSync(){
    return autoCommitNoSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setRange(  long min,  long max){
    this.rangeMin=min;
    this.rangeMax=max;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getRangeMin(){
    return rangeMin;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getRangeMax(){
    return rangeMax;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setWrap(  boolean wrap){
    this.wrap=wrap;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getWrap(){
    return wrap;
  }
}
