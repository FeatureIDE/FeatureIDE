package com.sleepycat.je;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class OperationStatus {
  /** 
 * Javadoc for this public instance is generated via
 * the doc templates in the doc_src directory.
 */
  public static final OperationStatus SUCCESS=new OperationStatus("SUCCESS");
  /** 
 * Javadoc for this public instance is generated via
 * the doc templates in the doc_src directory.
 */
  public static final OperationStatus KEYEXIST=new OperationStatus("KEYEXIST");
  /** 
 * Javadoc for this public instance is generated via
 * the doc templates in the doc_src directory.
 */
  public static final OperationStatus KEYEMPTY=new OperationStatus("KEYEMPTY");
  /** 
 * Javadoc for this public instance is generated via
 * the doc templates in the doc_src directory.
 */
  public static final OperationStatus NOTFOUND=new OperationStatus("NOTFOUND");
  private String statusName;
  private OperationStatus(  String statusName){
    this.statusName=statusName;
  }
  public String toString(){
    return "OperationStatus." + statusName;
  }
}
