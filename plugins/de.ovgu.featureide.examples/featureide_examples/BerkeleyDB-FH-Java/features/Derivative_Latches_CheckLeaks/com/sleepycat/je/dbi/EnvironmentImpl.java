package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  protected void hook311() throws DatabaseException {
    LatchSupport.clearNotes();
    original();
  }
@MethodObject static class EnvironmentImpl_checkLeaks {
    protected void hook312() throws DatabaseException {
      if (LatchSupport.countLatchesHeld() > 0) {
        clean=false;
        System.out.println("Some latches held at env close.");
        LatchSupport.dumpLatchesHeld();
      }
      original();
    }
  }
}
