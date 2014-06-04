package com.sleepycat.je.txn;
public abstract class Locker {
  protected Map deleteInfo;
  /** 
 * Add delete information, to be added to the inCompressor queue
 * when the transaction ends.
 */
  public void addDeleteInfo(  BIN bin,  Key deletedKey) throws DatabaseException {
synchronized (this) {
      if (deleteInfo == null) {
        deleteInfo=new HashMap();
      }
      Long nodeId=new Long(bin.getNodeId());
      BINReference binRef=(BINReference)deleteInfo.get(nodeId);
      if (binRef == null) {
        binRef=bin.createReference();
        deleteInfo.put(nodeId,binRef);
      }
      binRef.addDeletedKey(deletedKey);
    }
  }
}
