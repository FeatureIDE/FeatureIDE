package com.sleepycat.je.utilint;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import de.ovgu.cide.jakutil.*;
/** 
 * Bitmap which supports indexing with long arguments. java.util.BitSet
 * provides all the functionality and performance we need, but requires integer
 * indexing.
 * Long indexing is implemented by keeping a Map of java.util.BitSets, where
 * each bitset covers 2^16 bits worth of values. The Bitmap may be sparse, in
 * that each segment is only instantiated when needed.
 * Note that this class is currently not thread safe; adding a new bitset
 * segment is not protected.
 */
public class BitMap {
  private static final int SEGMENT_SIZE=16;
  private static final int SEGMENT_MASK=0xffff;
  private Map bitSegments;
  public BitMap(){
    bitSegments=new HashMap();
  }
  public void set(  long index) throws IndexOutOfBoundsException {
    if (index < 0) {
      throw new IndexOutOfBoundsException(index + " is negative.");
    }
    BitSet bitset=getBitSet(index,true);
    if (bitset == null) {
      throw new IllegalArgumentException(index + " is out of bounds");
    }
    int useIndex=getIntIndex(index);
    bitset.set(useIndex);
  }
  public boolean get(  long index) throws IndexOutOfBoundsException {
    if (index < 0) {
      throw new IndexOutOfBoundsException(index + " is negative.");
    }
    BitSet bitset=getBitSet(index,false);
    if (bitset == null) {
      return false;
    }
    int useIndex=getIntIndex(index);
    return bitset.get(useIndex);
  }
  private BitSet getBitSet(  long index,  boolean allowCreate){
    Long segmentId=new Long(index >> SEGMENT_SIZE);
    BitSet bitset=(BitSet)bitSegments.get(segmentId);
    if (allowCreate) {
      if (bitset == null) {
        bitset=new BitSet();
        bitSegments.put(segmentId,bitset);
      }
    }
    return bitset;
  }
  private int getIntIndex(  long index){
    return (int)(index & SEGMENT_MASK);
  }
  int getNumSegments(){
    return bitSegments.size();
  }
  int cardinality(){
    int count=0;
    Iterator iter=bitSegments.values().iterator();
    while (iter.hasNext()) {
      BitSet b=(BitSet)iter.next();
      count+=b.cardinality();
    }
    return count;
  }
}
