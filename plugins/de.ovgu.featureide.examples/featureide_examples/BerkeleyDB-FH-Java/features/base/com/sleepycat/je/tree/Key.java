package com.sleepycat.je.tree;
import java.util.Comparator;
import com.sleepycat.je.DatabaseEntry;
import de.ovgu.cide.jakutil.*;
/** 
 * Key represents a JE B-Tree Key.  Keys are immutable.  Within JE, keys are
 * usually represented as byte arrays rather than as Key instances in order to
 * reduce the in-memory footprint. The static methods of this class are used to
 * operate on the byte arrays.
 * One exception is when keys are held within a collection. In that case, Key
 * objects are instantiated so that keys are hashed and compared by value.
 */
public final class Key implements Comparable {
  public static boolean DUMP_BINARY=true;
  public static boolean DUMP_INT_BINDING=false;
  public static final byte[] EMPTY_KEY=new byte[0];
  private byte[] key;
  /** 
 * Construct a new key from a byte array.
 */
  public Key(  byte[] key){
    if (key == null) {
      this.key=null;
    }
 else {
      this.key=new byte[key.length];
      System.arraycopy(key,0,this.key,0,key.length);
    }
  }
  public static byte[] makeKey(  DatabaseEntry dbt){
    byte[] entryKey=dbt.getData();
    if (entryKey == null) {
      return EMPTY_KEY;
    }
 else {
      byte[] newKey=new byte[dbt.getSize()];
      System.arraycopy(entryKey,dbt.getOffset(),newKey,0,dbt.getSize());
      return newKey;
    }
  }
  /** 
 * Get the byte array for the key.
 */
  public byte[] getKey(){
    return key;
  }
  /** 
 * Compare two keys.  Standard compareTo function and returns.
 * Note that any configured user comparison function is not used, and
 * therefore this method should not be used for comparison of keys during
 * Btree operations.
 */
  public int compareTo(  Object o){
    if (o == null) {
      throw new NullPointerException();
    }
    Key argKey=(Key)o;
    return compareUnsignedBytes(this.key,argKey.key);
  }
  /** 
 * Support Set of Key in BINReference.
 */
  public boolean equals(  Object o){
    return (o instanceof Key) && (compareTo(o) == 0);
  }
  /** 
 * Support HashSet of Key in BINReference.
 */
  public int hashCode(){
    int code=0;
    for (int i=0; i < key.length; i+=1) {
      code+=key[i];
    }
    return code;
  }
  /** 
 * Compare keys with an optional comparator.
 */
  public static int compareKeys(  byte[] key1,  byte[] key2,  Comparator comparator){
    if (comparator != null) {
      return comparator.compare(key1,key2);
    }
 else {
      return compareUnsignedBytes(key1,key2);
    }
  }
  /** 
 * Compare using a default unsigned byte comparison.
 */
  private static int compareUnsignedBytes(  byte[] key1,  byte[] key2){
    int a1Len=key1.length;
    int a2Len=key2.length;
    int limit=Math.min(a1Len,a2Len);
    for (int i=0; i < limit; i++) {
      byte b1=key1[i];
      byte b2=key2[i];
      if (b1 == b2) {
        continue;
      }
 else {
        return (b1 & 0xff) - (b2 & 0xff);
      }
    }
    return (a1Len - a2Len);
  }
  public static String dumpString(  byte[] key,  int nspaces){
    StringBuffer sb=new StringBuffer();
    sb.append(TreeUtils.indent(nspaces));
    sb.append("<key v=\"");
    if (DUMP_BINARY) {
      if (key == null) {
        sb.append("<null>");
      }
 else {
        sb.append(TreeUtils.dumpByteArray(key));
      }
    }
 else     if (DUMP_INT_BINDING) {
      if (key == null) {
        sb.append("<null>");
      }
 else {
        DatabaseEntry e=new DatabaseEntry(key);
      }
    }
 else {
      sb.append(key == null ? "" : new String(key));
    }
    sb.append("\"/>");
    return sb.toString();
  }
  /** 
 * Print the string w/out XML format.
 */
  public static String getNoFormatString(  byte[] key){
    return "key=" + dumpString(key,0);
  }
}
