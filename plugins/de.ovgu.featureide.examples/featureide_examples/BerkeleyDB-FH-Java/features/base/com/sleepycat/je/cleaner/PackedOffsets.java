package com.sleepycat.je.cleaner;
import java.nio.ByteBuffer;
import java.util.Arrays;
import com.sleepycat.je.log.LogReadable;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LogWritable;
import de.ovgu.cide.jakutil.*;
/** 
 * Stores a sorted list of LSN offsets in a packed short representation.  Each
 * stored value is the difference between two consecutive offsets.  The stored
 * values are stored as one or more shorts where each short holds 0x7fff
 * values.  Shorts are in LSB order.  The value is negated if more shorts for
 * the same offset follow; this works because offsets are always positive
 * values.
 */
public class PackedOffsets implements LogWritable, LogReadable {
  private short[] data;
  private int size;
  /** 
 * Creates an empty object.
 */
  public PackedOffsets(){
  }
  /** 
 * Returns an iterator over all offsets.
 */
  Iterator iterator(){
    return new Iterator();
  }
  /** 
 * Packs the given offsets, replacing any offsets stored in this object.
 */
  public void pack(  long[] offsets){
    short[] newData=new short[offsets.length * 3];
    Arrays.sort(offsets);
    int dataIndex=0;
    long priorVal=0;
    for (int i=0; i < offsets.length; i+=1) {
      long val=offsets[i];
      dataIndex=append(newData,dataIndex,val - priorVal);
      priorVal=val;
    }
    data=new short[dataIndex];
    System.arraycopy(newData,0,data,0,dataIndex);
    size=offsets.length;
  }
  /** 
 * Returns the unpacked offsets.
 */
  long[] toArray(){
    long[] offsets=new long[size];
    int index=0;
    Iterator iter=iterator();
    while (iter.hasNext()) {
      offsets[index++]=iter.next();
    }
    assert index == size;
    return offsets;
  }
  /** 
 * Copies the given value as a packed long to the array starting at the
 * given index.  Returns the index of the next position in the array.
 */
  private int append(  short[] to,  int index,  long val){
    assert val >= 0;
    while (true) {
      short s=(short)(val & 0x7fff);
      val>>>=15;
      if (val > 0) {
        to[index++]=(short)(-1 - s);
      }
 else {
        to[index++]=s;
        break;
      }
    }
    return index;
  }
  /** 
 * An iterator over all offsets.
 */
class Iterator {
    private int index;
    private long priorVal;
    private Iterator(){
    }
    boolean hasNext(){
      return data != null && index < data.length;
    }
    long next(){
      long val=priorVal;
      for (int shift=0; ; shift+=15) {
        long s=data[index++];
        if (s < 0) {
          val+=(-1 - s) << shift;
        }
 else {
          val+=s << shift;
          break;
        }
      }
      priorVal=val;
      return val;
    }
  }
  /** 
 * @see LogWritable#getLogSize
 */
  public int getLogSize(){
    return (2 * LogUtils.getIntLogSize()) + ((data != null) ? (data.length * LogUtils.SHORT_BYTES) : 0);
  }
  /** 
 * @see LogWritable#writeToLog
 */
  public void writeToLog(  ByteBuffer buf){
    LogUtils.writeInt(buf,size);
    if (data != null) {
      LogUtils.writeInt(buf,data.length);
      for (int i=0; i < data.length; i+=1) {
        LogUtils.writeShort(buf,data[i]);
      }
    }
 else {
      LogUtils.writeInt(buf,0);
    }
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer buf,  byte entryTypeVersion){
    size=LogUtils.readInt(buf);
    int len=LogUtils.readInt(buf);
    if (len > 0) {
      data=new short[len];
      for (int i=0; i < len; i+=1) {
        data[i]=LogUtils.readShort(buf);
      }
    }
  }
  /** 
 * @see LogReadable#dumpLog
 */
  public void dumpLog(  StringBuffer buf,  boolean verbose){
    if (size > 0) {
      Iterator i=iterator();
      buf.append("<offsets size=\"");
      buf.append(size);
      buf.append("\">");
      while (i.hasNext()) {
        buf.append("0x");
        buf.append(Long.toHexString(i.next()));
        buf.append(' ');
      }
      buf.append("</offsets>");
    }
 else {
      buf.append("<offsets size=\"0\"/>");
    }
  }
  /** 
 * Never called.
 * @see LogReadable#getTransactionId
 */
  public long getTransactionId(){
    return -1;
  }
  /** 
 * Never called.
 * @see LogReadable#logEntryIsTransactional
 */
  public boolean logEntryIsTransactional(){
    return false;
  }
  public String toString(){
    StringBuffer buf=new StringBuffer();
    dumpLog(buf,true);
    return buf.toString();
  }
}
