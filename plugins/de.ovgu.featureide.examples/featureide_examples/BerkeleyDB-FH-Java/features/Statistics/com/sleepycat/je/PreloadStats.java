package com.sleepycat.je;
public class PreloadStats {
  /** 
 * The number of INs, BINs, LNs, DINs, DBINs, and DupCountLNs loaded during
 * the preload() operation.
 */
  public int nINsLoaded;
  public int nBINsLoaded;
  public int nLNsLoaded;
  public int nDINsLoaded;
  public int nDBINsLoaded;
  public int nDupCountLNsLoaded;
  /** 
 * The status of the preload() operation.
 */
  public PreloadStatus status;
  /** 
 * Resets all stats.
 */
  private void reset(){
    nINsLoaded=0;
    nBINsLoaded=0;
    nLNsLoaded=0;
    nDINsLoaded=0;
    nDBINsLoaded=0;
    nDupCountLNsLoaded=0;
    status=PreloadStatus.SUCCESS;
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public int getNINsLoaded(){
    return nINsLoaded;
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public int getNBINsLoaded(){
    return nBINsLoaded;
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public int getNLNsLoaded(){
    return nLNsLoaded;
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public int getNDINsLoaded(){
    return nDINsLoaded;
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public int getNDBINsLoaded(){
    return nDBINsLoaded;
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public int getNDupCountLNsLoaded(){
    return nDupCountLNsLoaded;
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public PreloadStatus getStatus(){
    return status;
  }
  /** 
 * Internal use only.
 */
  public void setNINsLoaded(  int nINsLoaded){
    this.nINsLoaded=nINsLoaded;
  }
  /** 
 * Internal use only.
 */
  public void setNBINsLoaded(  int nBINsLoaded){
    this.nBINsLoaded=nBINsLoaded;
  }
  /** 
 * Internal use only.
 */
  public void setNLNsLoaded(  int nLNsLoaded){
    this.nLNsLoaded=nLNsLoaded;
  }
  /** 
 * Internal use only.
 */
  public void setNDINsLoaded(  int nDINsLoaded){
    this.nDINsLoaded=nDINsLoaded;
  }
  /** 
 * Internal use only.
 */
  public void setNDBINsLoaded(  int nDBINsLoaded){
    this.nDBINsLoaded=nDBINsLoaded;
  }
  /** 
 * Internal use only.
 */
  public void setNDupCountLNsLoaded(  int nDupCountLNsLoaded){
    this.nDupCountLNsLoaded=nDupCountLNsLoaded;
  }
  /** 
 * Internal use only.
 */
  public void setStatus(  PreloadStatus status){
    this.status=status;
  }
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public String toString(){
    StringBuffer sb=new StringBuffer();
    sb.append("status=").append(status).append('\n');
    sb.append("nINsLoaded=").append(nINsLoaded).append('\n');
    sb.append("nBINsLoaded=").append(nBINsLoaded).append('\n');
    sb.append("nLNsLoaded=").append(nLNsLoaded).append('\n');
    sb.append("nDINsLoaded=").append(nDINsLoaded).append('\n');
    sb.append("nDBINsLoaded=").append(nDBINsLoaded).append('\n');
    sb.append("nDupCountLNsLoaded=").append(nDupCountLNsLoaded).append('\n');
    return sb.toString();
  }
  /** 
 * Internal use only.
 */
  PreloadStats(){
    reset();
  }
}
