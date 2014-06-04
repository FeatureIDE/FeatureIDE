package com.sleepycat.je.util;
public class DbRunAction {
  private static final int REMOVEDB=5;
  private static void removeAndClean(  Environment env,  String name) throws DatabaseException {
    long a, b, c, d, e, f;
    Transaction txn=env.beginTransaction(null,null);
    CheckpointConfig force=new CheckpointConfig();
    force.setForce(true);
    a=System.currentTimeMillis();
    env.removeDatabase(txn,name);
    b=System.currentTimeMillis();
    txn.commit();
    c=System.currentTimeMillis();
    int cleanedCount=0;
    while (env.cleanLog() > 0) {
      cleanedCount++;
    }
    d=System.currentTimeMillis();
    System.out.println("cleanedCount=" + cleanedCount);
    e=0;
    f=0;
    if (cleanedCount > 0) {
      e=System.currentTimeMillis();
      env.checkpoint(force);
      f=System.currentTimeMillis();
    }
    System.out.println("Remove of " + name + " remove: "+ getSecs(a,b)+ " commit: "+ getSecs(b,c)+ " clean: "+ getSecs(c,d)+ " checkpoint: "+ getSecs(e,f));
  }
@MethodObject static class DbRunAction_main {
    protected void hook842() throws Exception {
      if (doAction == REMOVEDB) {
        removeAndClean(env,dbName);
      }
      original();
    }
    protected void hook843() throws Exception {
      if (action.equalsIgnoreCase("removedb")) {
        doAction=REMOVEDB;
      }
 else {
        original();
      }
    }
  }
}
