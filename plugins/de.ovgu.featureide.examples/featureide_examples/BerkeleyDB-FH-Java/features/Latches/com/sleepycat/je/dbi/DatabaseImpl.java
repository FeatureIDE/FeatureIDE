package com.sleepycat.je.dbi;
import com.sleepycat.je.latch.LatchSupport;
public class DatabaseImpl {
@MethodObject static class DatabaseImpl_preload {
    PreloadStats execute() throws DatabaseException {
      PreloadStats result=original();
      assert LatchSupport.countLatchesHeld() == 0;
      return result;
    }
  }
}
