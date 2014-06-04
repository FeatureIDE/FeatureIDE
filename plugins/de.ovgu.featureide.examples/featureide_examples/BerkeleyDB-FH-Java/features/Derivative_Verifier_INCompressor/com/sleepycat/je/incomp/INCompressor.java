package com.sleepycat.je.incomp;
public class INCompressor {
  public synchronized void verifyCursors() throws DatabaseException {
    if (env.isClosed()) {
      return;
    }
    List queueSnapshot=null;
synchronized (binRefQueueSync) {
      queueSnapshot=new ArrayList(binRefQueue.values());
    }
    Map dbCache=new HashMap();
    Iterator it=queueSnapshot.iterator();
    while (it.hasNext()) {
      BINReference binRef=(BINReference)it.next();
      DatabaseImpl db=env.getDbMapTree().getDb(binRef.getDatabaseId(),lockTimeout,dbCache);
      BIN bin=searchForBIN(db,binRef);
      if (bin != null) {
        bin.verifyCursors();
        this.hook390(bin);
      }
    }
  }
  protected void hook390(  BIN bin) throws DatabaseException {
  }
}
