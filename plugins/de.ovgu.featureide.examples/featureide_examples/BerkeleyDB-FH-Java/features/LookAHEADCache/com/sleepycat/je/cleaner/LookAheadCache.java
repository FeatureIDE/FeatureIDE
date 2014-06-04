package com.sleepycat.je.cleaner;
import java.util.SortedMap;
import java.util.TreeMap;
import com.sleepycat.je.dbi.MemoryBudget;
import de.ovgu.cide.jakutil.*;
/** 
 * A cache of LNInfo by LSN offset. Used to hold a set of LNs that are to be
 * processed. Keeps track of memory used, and when full (over budget) the next
 * offset should be queried and removed.
 */
class LookAheadCache {
  private SortedMap map;
  private int maxMem;
  private int usedMem;
  LookAheadCache(  int lookAheadCacheSize){
    map=new TreeMap();
    maxMem=lookAheadCacheSize;
  }
  boolean isEmpty(){
    return map.isEmpty();
  }
  boolean isFull(){
    return usedMem >= maxMem;
  }
  Long nextOffset(){
    return (Long)map.firstKey();
  }
  void add(  Long lsnOffset,  LNInfo info){
    map.put(lsnOffset,info);
    usedMem++;
    this.hook166(info);
  }
  LNInfo remove(  Long offset){
    LNInfo info=(LNInfo)map.remove(offset);
    if (info != null) {
      this.hook167(info);
    }
    return info;
  }
  protected void hook166(  LNInfo info){
  }
  protected void hook167(  LNInfo info){
  }
}
