package com.sleepycat.je.tree;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
public class TreeLocation {
  public BIN bin;
  public int index;
  public byte[] lnKey;
  public long childLsn=DbLsn.NULL_LSN;
  public void reset(){
    bin=null;
    index=-1;
    lnKey=null;
    childLsn=DbLsn.NULL_LSN;
  }
  public String toString(){
    StringBuffer sb=new StringBuffer("<TreeLocation bin=\"");
    if (bin == null) {
      sb.append("null");
    }
 else {
      sb.append(bin.getNodeId());
    }
    sb.append("\" index=\"");
    sb.append(index);
    sb.append("\" lnKey=\"");
    sb.append(Key.dumpString(lnKey,0));
    sb.append("\" childLsn=\"");
    sb.append(DbLsn.toString(childLsn));
    sb.append("\">");
    return sb.toString();
  }
}
