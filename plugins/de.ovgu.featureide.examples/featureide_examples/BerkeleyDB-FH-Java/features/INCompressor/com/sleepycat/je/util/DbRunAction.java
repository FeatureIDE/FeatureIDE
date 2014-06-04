package com.sleepycat.je.util;
public class DbRunAction {
  private static final int COMPRESS=2;
@MethodObject static class DbRunAction_main {
    protected void hook840() throws Exception {
      if (doAction == COMPRESS) {
        env.compress();
      }
      original();
    }
    protected void hook841() throws Exception {
      if (action.equalsIgnoreCase("compress")) {
        doAction=COMPRESS;
      }
 else {
        original();
      }
    }
  }
}
