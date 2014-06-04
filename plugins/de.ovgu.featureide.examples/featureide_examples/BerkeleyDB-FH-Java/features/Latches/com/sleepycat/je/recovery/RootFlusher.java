/** 
 */
package com.sleepycat.je.recovery;
class RootFlusher {
  protected void hook599(  ChildReference root,  IN rootIN) throws DatabaseException {
    rootIN.latch(false);
    try {
      original(root,rootIN);
    }
  finally {
      rootIN.releaseLatch();
    }
  }
}
