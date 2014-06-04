package com.sleepycat.je.latch;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;
import de.ovgu.cide.jakutil.*;
/** 
 * Table of latches by thread for debugging.
 */
class LatchTable {
  private String tableName;
  private Map latchesByThread;
  LatchTable(  String tableName){
    this.tableName=tableName;
    latchesByThread=Collections.synchronizedMap(new WeakHashMap());
  }
  /** 
 * Only call under the assert system. This records latching by thread.
 */
  boolean noteLatch(  Object latch) throws LatchException {
    Thread cur=Thread.currentThread();
    Set threadLatches=(Set)latchesByThread.get(cur);
    if (threadLatches == null) {
      threadLatches=new HashSet();
      latchesByThread.put(cur,threadLatches);
    }
    threadLatches.add(latch);
    return true;
  }
  /** 
 * Only call under the assert system. This records latching by thread.
 * @return true if unnoted successfully.
 */
  boolean unNoteLatch(  Object latch,  String name){
    Thread cur=Thread.currentThread();
    Set threadLatches=(Set)latchesByThread.get(cur);
    if (threadLatches == null) {
      return false;
    }
 else {
      return threadLatches.remove(latch);
    }
  }
  /** 
 * Only call under the assert system. This counts held latches.
 */
  int countLatchesHeld(){
    Thread cur=Thread.currentThread();
    Set threadLatches=(Set)latchesByThread.get(cur);
    if (threadLatches != null) {
      return threadLatches.size();
    }
 else {
      return 0;
    }
  }
  String latchesHeldToString(){
    Thread cur=Thread.currentThread();
    Set threadLatches=(Set)latchesByThread.get(cur);
    StringBuffer sb=new StringBuffer();
    if (threadLatches != null) {
      Iterator i=threadLatches.iterator();
      while (i.hasNext()) {
        sb.append(i.next()).append('\n');
      }
    }
    return sb.toString();
  }
  void clearNotes(){
    latchesByThread.clear();
  }
  /** 
 * For concocting exception messages.
 */
  String getNameString(  String name){
    StringBuffer sb=new StringBuffer(tableName);
    if (name != null) {
      sb.append("(").append(name).append(")");
    }
    return sb.toString();
  }
  /** 
 * Formats a latch owner and waiters.
 */
  String toString(  String name,  Object owner,  List waiters,  int startIndex){
    StringBuffer sb=new StringBuffer();
    sb.append("<LATCH ");
    if (name != null) {
      sb.append("[name: ").append(name).append("] ");
    }
    sb.append("[owner: ").append(owner).append("]");
    if (waiters != null && waiters.size() > startIndex) {
      sb.append(" [waiters: ");
      for (int i=startIndex; i < waiters.size(); i++) {
        sb.append(waiters.get(i)).append(" ");
      }
      sb.append("]");
    }
    sb.append(">");
    return sb.toString();
  }
}
