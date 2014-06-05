package com.sleepycat.je.tree;
public class BIN {
  /** 
 * Reduce memory consumption by evicting all LN targets. Note that the
 * targets are not persistent, so this doesn't affect node dirtiness.
 * The BIN should be latched by the caller.
 * @return number of evicted bytes
 */
  public long evictLNs() throws DatabaseException {
    assert isLatchOwner() : "BIN must be latched before evicting LNs";
    return original();
  }
}
