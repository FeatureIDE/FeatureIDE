package com.sleepycat.je;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class TransactionConfig implements Cloneable {
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public static final TransactionConfig DEFAULT=new TransactionConfig();
  private boolean sync=false;
  private boolean noSync=false;
  private boolean writeNoSync=false;
  private boolean noWait=false;
  private boolean readUncommitted=false;
  private boolean readCommitted=false;
  private boolean serializableIsolation=false;
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public TransactionConfig(){
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setSync(  boolean sync){
    this.sync=sync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getSync(){
    return sync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setNoSync(  boolean noSync){
    this.noSync=noSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getNoSync(){
    return noSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setWriteNoSync(  boolean writeNoSync){
    this.writeNoSync=writeNoSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getWriteNoSync(){
    return writeNoSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setNoWait(  boolean noWait){
    this.noWait=noWait;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getNoWait(){
    return noWait;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setReadUncommitted(  boolean readUncommitted){
    this.readUncommitted=readUncommitted;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getReadUncommitted(){
    return readUncommitted;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 * @deprecated
 */
  public void setDirtyRead(  boolean dirtyRead){
    setReadUncommitted(dirtyRead);
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 * @deprecated
 */
  public boolean getDirtyRead(){
    return getReadUncommitted();
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setReadCommitted(  boolean readCommitted){
    this.readCommitted=readCommitted;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getReadCommitted(){
    return readCommitted;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setSerializableIsolation(  boolean serializableIsolation){
    this.serializableIsolation=serializableIsolation;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getSerializableIsolation(){
    return serializableIsolation;
  }
  /** 
 * Used by Environment to create a copy of the application
 * supplied configuration. Done this way to provide non-public cloning.
 */
  TransactionConfig cloneConfig(){
    try {
      return (TransactionConfig)super.clone();
    }
 catch (    CloneNotSupportedException willNeverOccur) {
      return null;
    }
  }
}
