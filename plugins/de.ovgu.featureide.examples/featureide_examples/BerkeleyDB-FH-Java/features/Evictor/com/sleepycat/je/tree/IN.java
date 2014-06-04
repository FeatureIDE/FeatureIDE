package com.sleepycat.je.tree;
public class IN {
  public static final int MAY_NOT_EVICT=0;
  public static final int MAY_EVICT_LNS=1;
  public static final int MAY_EVICT_NODE=2;
  /** 
 * Returns whether this node can itself be evicted.  This is faster than
 * (getEvictionType() == MAY_EVICT_NODE) and is used by the evictor after
 * a node has been selected, to check that it is still evictable.
 */
  public boolean isEvictable(){
    if (isEvictionProhibited()) {
      return false;
    }
    if (hasNonLNChildren()) {
      return false;
    }
    return true;
  }
  /** 
 * Returns the eviction type for this IN, for use by the evictor.  Uses the
 * internal isEvictionProhibited and getChildEvictionType methods that may
 * be overridden by subclasses.
 * @return MAY_EVICT_LNS if evictable LNs may be stripped; otherwise,
 * MAY_EVICT_NODE if the node itself may be evicted; otherwise,
 * MAY_NOT_EVICT.
 */
  public int getEvictionType(){
    if (isEvictionProhibited()) {
      return MAY_NOT_EVICT;
    }
 else {
      return getChildEvictionType();
    }
  }
  /** 
 * Returns whether the node is not evictable, irrespective of the status
 * of the children nodes.
 */
  boolean isEvictionProhibited(){
    return isDbRoot();
  }
  /** 
 * Returns the eviction type based on the status of child nodes,
 * irrespective of isEvictionProhibited.
 */
  int getChildEvictionType(){
    return hasResidentChildren() ? MAY_NOT_EVICT : MAY_EVICT_NODE;
  }
}
