package com.sleepycat.je.tree;
public class IN {
@MethodObject static class IN_splitInternal {
    protected void hook636() throws DatabaseException {
      if (deletedEntrySeen) {
        _this.databaseImpl.getDbEnvironment().addToCompressorQueue(binRef,false);
      }
      original();
    }
  }
}
