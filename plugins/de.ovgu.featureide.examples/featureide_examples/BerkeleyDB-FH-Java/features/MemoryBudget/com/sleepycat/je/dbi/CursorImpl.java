package com.sleepycat.je.dbi;
public class CursorImpl {
  protected long hook283(  LN ln,  long newLNSize) throws DatabaseException {
    newLNSize=ln.getMemorySizeIncludedByParent();
    return original(ln,newLNSize);
  }
  protected long hook284(  LN ln,  long oldLNSize) throws DatabaseException {
    oldLNSize=ln.getMemorySizeIncludedByParent();
    return original(ln,oldLNSize);
  }
  protected long hook285(  LN ln,  long newLNSize) throws DatabaseException {
    newLNSize=ln.getMemorySizeIncludedByParent();
    return original(ln,newLNSize);
  }
  protected long hook286(  LN ln,  long oldLNSize) throws DatabaseException {
    oldLNSize=ln.getMemorySizeIncludedByParent();
    return original(ln,oldLNSize);
  }
}
