package com.sleepycat.je;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated via
 * the doc templates in the doc_src directory.
 */
public class ForeignKeyDeleteAction {
  private String name;
  private ForeignKeyDeleteAction(  String name){
    this.name=name;
  }
  /** 
 * Javadoc for this public class is generated via
 * the doc templates in the doc_src directory.
 */
  public final static ForeignKeyDeleteAction ABORT=new ForeignKeyDeleteAction("ABORT");
  /** 
 * Javadoc for this public class is generated via
 * the doc templates in the doc_src directory.
 */
  public final static ForeignKeyDeleteAction CASCADE=new ForeignKeyDeleteAction("CASCADE");
  /** 
 * Javadoc for this public class is generated via
 * the doc templates in the doc_src directory.
 */
  public final static ForeignKeyDeleteAction NULLIFY=new ForeignKeyDeleteAction("NULLIFY");
  public String toString(){
    return "ForeignKeyDeleteAction." + name;
  }
}
