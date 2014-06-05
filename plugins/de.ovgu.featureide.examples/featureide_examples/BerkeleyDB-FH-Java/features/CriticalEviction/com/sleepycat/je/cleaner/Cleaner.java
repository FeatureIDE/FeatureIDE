package com.sleepycat.je.cleaner;
public class Cleaner {
  /** 
 * Whether the cleaner should participate in critical eviction. Ideally the
 * cleaner would not participate in eviction, since that would reduce the
 * cost of cleaning. However, the cleaner can add large numbers of nodes to
 * the cache. By not participating in eviction, other threads could be kept
 * in a constant state of eviction and would effectively starve. Therefore,
 * this setting is currently enabled.
 */
  static final boolean DO_CRITICAL_EVICTION=true;
@MethodObject static class Cleaner_processPending {
    protected void hook86() throws DatabaseException {
    }
    protected void hook114() throws DatabaseException {
      if (_this.DO_CRITICAL_EVICTION) {
        this.hook86();
      }
      original();
    }
  }
}
