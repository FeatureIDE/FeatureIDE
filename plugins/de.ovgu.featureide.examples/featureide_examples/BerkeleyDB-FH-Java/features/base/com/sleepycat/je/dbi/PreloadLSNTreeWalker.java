package com.sleepycat.je.dbi;
import java.util.HashMap;
import java.util.Map;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.PreloadConfig;
import com.sleepycat.je.tree.ChildReference;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.Node;
import com.sleepycat.je.tree.WithRootLatched;
import de.ovgu.cide.jakutil.*;
class PreloadLSNTreeWalker extends SortedLSNTreeWalker {
  private Map lsnINMap=new HashMap();
private static class INEntry {
    INEntry(    IN in,    int index){
      this.in=in;
      this.index=index;
    }
    IN in;
    int index;
  }
  PreloadLSNTreeWalker(  DatabaseImpl db,  TreeNodeProcessor callback,  PreloadConfig conf) throws DatabaseException {
    super(db,false,false,db.tree.getRootLsn(),callback);
    accumulateLNs=conf.getLoadLNs();
  }
private final class PreloadWithRootLatched implements WithRootLatched {
    public IN doWork(    ChildReference root) throws DatabaseException {
      walkInternal();
      return null;
    }
  }
  public void walk() throws DatabaseException {
    WithRootLatched preloadWRL=new PreloadWithRootLatched();
    dbImpl.getTree().withRootLatchedExclusive(preloadWRL);
  }
  protected IN getRootIN(  long rootLsn) throws DatabaseException {
    return dbImpl.getTree().getRootIN(false);
  }
  protected void addToLsnINMap(  Long lsn,  IN in,  int index){
    assert in.getDatabase() != null;
    lsnINMap.put(lsn,new INEntry(in,index));
  }
  protected Node fetchLSN(  long lsn) throws DatabaseException {
    try {
      INEntry inEntry=(INEntry)lsnINMap.remove(new Long(lsn));
      assert (inEntry != null);
      IN in=inEntry.in;
      this.hook352(lsn,inEntry,in);
      throw ReturnHack.returnObject;
    }
 catch (    ReturnObject r) {
      return (Node)r.value;
    }
  }
  protected void hook352(  long lsn,  INEntry inEntry,  IN in) throws DatabaseException {
    int index=inEntry.index;
    if (in.isEntryKnownDeleted(index) || in.getLsn(index) != lsn) {
      throw new ReturnObject(null);
    }
    throw new ReturnObject(in.fetchTarget(index));
  }
}
