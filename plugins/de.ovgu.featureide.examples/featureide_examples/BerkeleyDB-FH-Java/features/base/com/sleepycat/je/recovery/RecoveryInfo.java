package com.sleepycat.je.recovery;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * RecoveryInfo keeps information about recovery processing. 
 */
public class RecoveryInfo {
  public long lastUsedLsn=DbLsn.NULL_LSN;
  public long nextAvailableLsn=DbLsn.NULL_LSN;
  public long firstActiveLsn=DbLsn.NULL_LSN;
  public long checkpointStartLsn=DbLsn.NULL_LSN;
  public long checkpointEndLsn=DbLsn.NULL_LSN;
  public long useRootLsn=DbLsn.NULL_LSN;
  public long partialCheckpointStartLsn=DbLsn.NULL_LSN;
  public CheckpointEnd checkpointEnd;
  public long useMaxNodeId;
  public int useMaxDbId;
  public long useMaxTxnId;
  public int numMapINs;
  public int numOtherINs;
  public int numBinDeltas;
  public int numDuplicateINs;
  public int lnFound;
  public int lnNotFound;
  public int lnInserted;
  public int lnReplaced;
  public int nRepeatIteratorReads;
  public String toString(){
    StringBuffer sb=new StringBuffer();
    sb.append("Recovery Info");
    appendLsn(sb," lastUsed=",lastUsedLsn);
    appendLsn(sb," nextAvail=",nextAvailableLsn);
    appendLsn(sb," ckptStart=",checkpointStartLsn);
    appendLsn(sb," firstActive=",firstActiveLsn);
    appendLsn(sb," ckptEnd=",checkpointEndLsn);
    appendLsn(sb," useRoot=",useRootLsn);
    sb.append(" ckptEnd=<").append(checkpointEnd).append(">");
    sb.append(" useMaxNodeId=").append(useMaxNodeId);
    sb.append(" useMaxDbId=").append(useMaxDbId);
    sb.append(" useMaxTxnId=").append(useMaxTxnId);
    sb.append(" numMapINs=").append(numMapINs);
    sb.append(" numOtherINs=").append(numOtherINs);
    sb.append(" numBinDeltas=").append(numBinDeltas);
    sb.append(" numDuplicateINs=").append(numDuplicateINs);
    sb.append(" lnFound=").append(lnFound);
    sb.append(" lnNotFound=").append(lnNotFound);
    sb.append(" lnInserted=").append(lnInserted);
    sb.append(" lnReplaced=").append(lnReplaced);
    sb.append(" nRepeatIteratorReads=").append(nRepeatIteratorReads);
    return sb.toString();
  }
  private void appendLsn(  StringBuffer sb,  String name,  long lsn){
    if (lsn != DbLsn.NULL_LSN) {
      sb.append(name).append(DbLsn.getNoFormatString(lsn));
    }
  }
}
