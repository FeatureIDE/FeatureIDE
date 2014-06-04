package com.sleepycat.je;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class JoinConfig implements Cloneable {
  static JoinConfig DEFAULT=new JoinConfig();
  private boolean noSort;
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public JoinConfig(){
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setNoSort(  boolean noSort){
    this.noSort=noSort;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getNoSort(){
    return noSort;
  }
  /** 
 * Used by SecondaryDatabase to create a copy of the application
 * supplied configuration. Done this way to provide non-public cloning.
 */
  JoinConfig cloneConfig(){
    try {
      return (JoinConfig)super.clone();
    }
 catch (    CloneNotSupportedException willNeverOccur) {
      return null;
    }
  }
}
