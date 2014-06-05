package com.sleepycat.je.cleaner;
class FileSelector {
  private Set pendingDBs;
  /** 
 * Adds the given DatabaseId to the pending DB set.
 */
  synchronized boolean addPendingDB(  DatabaseId dbId){
    boolean added=pendingDBs.add(dbId);
    anyPendingDuringCheckpoint=true;
    return added;
  }
  /** 
 * Returns an array of DatabaseIds for DBs that were pending deletion in a
 * prior cleaning attempt, or null if no DBs are pending.
 */
  synchronized DatabaseId[] getPendingDBs(){
    if (pendingDBs.size() > 0) {
      DatabaseId[] dbs=new DatabaseId[pendingDBs.size()];
      pendingDBs.toArray(dbs);
      return dbs;
    }
 else {
      return null;
    }
  }
  /** 
 * Removes the DatabaseId from the pending DB set.
 */
  synchronized void removePendingDB(  DatabaseId dbId){
    pendingDBs.remove(dbId);
    updateProcessedFiles();
  }
  protected void hook163(){
    pendingDBs=new HashSet();
    original();
  }
  protected void hook164(){
    anyPendingDuringCheckpoint|=!pendingDBs.isEmpty();
    original();
  }
  protected boolean hook165(  boolean b){
    b&=pendingDBs.isEmpty();
    return original(b);
  }
}
