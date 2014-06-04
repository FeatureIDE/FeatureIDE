/** 
 */
package com.sleepycat.je.recovery;
class RootUpdater {
  protected void hook600() throws DatabaseException {
    inFromLog.releaseLatch();
    original();
  }
}
