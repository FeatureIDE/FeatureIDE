package com.sleepycat.je;
import java.io.Serializable;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class PreloadStatus implements Serializable {
  private String statusName;
  private PreloadStatus(  String statusName){
    this.statusName=statusName;
  }
  public String toString(){
    return "PreloadStatus." + statusName;
  }
  public static final PreloadStatus SUCCESS=new PreloadStatus("SUCCESS");
  public static final PreloadStatus FILLED_CACHE=new PreloadStatus("FILLED_CACHE");
  public static final PreloadStatus EXCEEDED_TIME=new PreloadStatus("EXCEEDED_TIME");
}
