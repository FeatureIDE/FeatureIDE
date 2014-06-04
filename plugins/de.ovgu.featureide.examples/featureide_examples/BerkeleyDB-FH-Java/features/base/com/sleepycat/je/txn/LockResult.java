package com.sleepycat.je.txn;
import com.sleepycat.je.tree.LN;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * This class is a container to encapsulate a LockGrantType and a WriteLockInfo
 * so that they can both be returned from writeLock.
 */
public class LockResult {
  private LockGrantType grant;
  private WriteLockInfo info;
  private LN ln;
  public LockResult(  LockGrantType grant,  WriteLockInfo info){
    this.grant=grant;
    this.info=info;
  }
  public LN getLN(){
    return ln;
  }
  public void setLN(  LN ln){
    this.ln=ln;
  }
  public LockGrantType getLockGrant(){
    return grant;
  }
  public void setAbortLsn(  long abortLsn,  boolean abortKnownDeleted){
    setAbortLsnInternal(abortLsn,abortKnownDeleted,false);
  }
  public void setAbortLsn(  long abortLsn,  boolean abortKnownDeleted,  boolean createdThisTxn){
    setAbortLsnInternal(abortLsn,abortKnownDeleted,createdThisTxn);
  }
  private void setAbortLsnInternal(  long abortLsn,  boolean abortKnownDeleted,  boolean createdThisTxn){
    if (info != null && info.neverLocked) {
      if (abortLsn != DbLsn.NULL_LSN) {
        info.abortLsn=abortLsn;
        info.abortKnownDeleted=abortKnownDeleted;
      }
      info.createdThisTxn=createdThisTxn;
      info.neverLocked=false;
    }
  }
}
