package com.sleepycat.je;
public class EnvironmentStats {
  private long nFSyncs;
  private long nFSyncRequests;
  private long nFSyncTimeouts;
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNFSyncs(){
    return nFSyncs;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNFSyncRequests(){
    return nFSyncRequests;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNFSyncTimeouts(){
    return nFSyncTimeouts;
  }
  /** 
 * Internal use only.
 */
  public void setNFSyncs(  long val){
    nFSyncs=val;
  }
  /** 
 * Internal use only.
 */
  public void setNFSyncRequests(  long val){
    nFSyncRequests=val;
  }
  /** 
 * Internal use only.
 */
  public void setNFSyncTimeouts(  long val){
    nFSyncTimeouts=val;
  }
  protected void hook60(){
    nFSyncs=0;
    nFSyncRequests=0;
    nFSyncTimeouts=0;
    original();
  }
  protected void hook61(  StringBuffer sb){
    sb.append("nFSyncs=").append(nFSyncs).append('\n');
    sb.append("nFSyncRequests=").append(nFSyncRequests).append('\n');
    sb.append("nFSyncTimeouts=").append(nFSyncTimeouts).append('\n');
    original(sb);
  }
}
