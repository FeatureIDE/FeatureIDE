package com.sleepycat.bind;
import com.sleepycat.je.DatabaseEntry;
import de.ovgu.cide.jakutil.*;
/** 
 * A pass-through <code>EntryBinding</code> that uses the entry's byte array
 * as the key or data object.
 * @author Mark Hayes
 */
public class ByteArrayBinding implements EntryBinding {
  private static byte[] ZERO_LENGTH_BYTE_ARRAY=new byte[0];
  /** 
 * Creates a byte array binding.
 */
  public ByteArrayBinding(){
  }
  public Object entryToObject(  DatabaseEntry entry){
    int len=entry.getSize();
    if (len == 0) {
      return ZERO_LENGTH_BYTE_ARRAY;
    }
 else {
      byte[] bytes=new byte[len];
      System.arraycopy(entry.getData(),entry.getOffset(),bytes,0,bytes.length);
      return bytes;
    }
  }
  public void objectToEntry(  Object object,  DatabaseEntry entry){
    byte[] bytes=(byte[])object;
    entry.setData(bytes,0,bytes.length);
  }
}
