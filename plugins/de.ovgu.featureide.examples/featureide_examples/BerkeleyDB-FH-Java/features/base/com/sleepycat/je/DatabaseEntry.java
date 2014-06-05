package com.sleepycat.je;
import com.sleepycat.je.tree.TreeUtils;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class DatabaseEntry {
  private byte[] data;
  private int dlen=0;
  private int doff=0;
  private int offset=0;
  private int size=0;
  private boolean partial=false;
  public String toString(){
    StringBuffer sb=new StringBuffer("<DatabaseEntry");
    sb.append(" dlen=").append(dlen);
    sb.append(" doff=").append(doff);
    sb.append(" doff=").append(doff);
    sb.append(" offset=").append(offset);
    sb.append(" size=").append(size);
    sb.append(">");
    return sb.toString();
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public DatabaseEntry(){
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public DatabaseEntry(  byte[] data){
    this.data=data;
    if (data != null) {
      this.size=data.length;
    }
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public DatabaseEntry(  byte[] data,  int offset,  int size){
    this.data=data;
    this.offset=offset;
    this.size=size;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public byte[] getData(){
    return data;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setData(  byte[] data){
    this.data=data;
    offset=0;
    size=(data == null) ? 0 : data.length;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setData(  byte[] data,  int offset,  int size){
    this.data=data;
    this.offset=offset;
    this.size=size;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setPartial(  int doff,  int dlen,  boolean partial){
    setPartialOffset(doff);
    setPartialLength(dlen);
    setPartial(partial);
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getPartialLength(){
    return dlen;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setPartialLength(  int dlen){
    this.dlen=dlen;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getPartialOffset(){
    return doff;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setPartialOffset(  int doff){
    this.doff=doff;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getPartial(){
    return partial;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setPartial(  boolean partial){
    this.partial=partial;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getOffset(){
    return offset;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setOffset(  int offset){
    this.offset=offset;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getSize(){
    return size;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setSize(  int size){
    this.size=size;
  }
  /** 
 * Dumps the data as a byte array, for tracing purposes
 */
  String dumpData(){
    return TreeUtils.dumpByteArray(data);
  }
  /** 
 * Compares the data of two entries for byte-by-byte equality.
 * <p>In either entry, if the offset is non-zero or the size is not equal
 * to the data array length, then only the data bounded by these values is
 * compared.  The data array length and offset need not be the same in both
 * entries for them to be considered equal.</p>
 * <p>If the data array is null in one entry, then to be considered equal
 * both entries must have a null data array.</p>
 * <p>If the partial property is set in either entry, then to be considered
 * equal both entries must have the same partial properties: partial,
 * partialOffset and partialLength.
 */
  public boolean equals(  Object o){
    if (!(o instanceof DatabaseEntry)) {
      return false;
    }
    DatabaseEntry e=(DatabaseEntry)o;
    if (partial || e.partial) {
      if (partial != e.partial || dlen != e.dlen || doff != e.doff) {
        return false;
      }
    }
    if (data == null && e.data == null) {
      return true;
    }
    if (data == null || e.data == null) {
      return false;
    }
    if (size != e.size) {
      return false;
    }
    for (int i=0; i < size; i+=1) {
      if (data[offset + i] != e.data[e.offset + i]) {
        return false;
      }
    }
    return true;
  }
  /** 
 * Returns a hash code based on the data value.
 */
  public int hashCode(){
    int hash=0;
    if (data != null) {
      for (int i=0; i < size; i+=1) {
        hash+=data[offset + i];
      }
    }
    return hash;
  }
}
