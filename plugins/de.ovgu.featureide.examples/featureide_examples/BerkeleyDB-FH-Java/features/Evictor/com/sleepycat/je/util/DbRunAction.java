package com.sleepycat.je.util;
public class DbRunAction {
  private static final int EVICT=3;
  private static void doEvict(  Environment env) throws DatabaseException {
    new DbRunAction_doEvict(env).execute();
  }
@MethodObject static class DbRunAction_doEvict {
    DbRunAction_doEvict(    Environment env){
      this.env=env;
    }
    void execute() throws DatabaseException {
      envImpl=DbInternal.envGetEnvironmentImpl(env);
      this.hook837();
      c=new EnvironmentMutableConfig();
      this.hook836();
      env.setMutableConfig(c);
      start=System.currentTimeMillis();
      env.evictMemory();
      end=System.currentTimeMillis();
      f=new DecimalFormat();
      f.setMaximumFractionDigits(2);
      System.out.println("evict time=" + f.format(end - start));
    }
    protected Environment env;
    protected EnvironmentImpl envImpl;
    protected long cacheUsage;
    protected EnvironmentMutableConfig c;
    protected long start;
    protected long end;
    protected DecimalFormat f;
    protected void hook836() throws DatabaseException {
    }
    protected void hook837() throws DatabaseException {
    }
  }
@MethodObject static class DbRunAction_main {
    protected void hook844() throws Exception {
      if (doAction == EVICT) {
        preload(env,dbName);
      }
      original();
    }
    protected void hook845() throws Exception {
      if (doAction == EVICT) {
        envConfig.setConfigParam(EnvironmentParams.ENV_RUN_EVICTOR.getName(),"false");
        envConfig.setConfigParam(EnvironmentParams.EVICTOR_CRITICAL_PERCENTAGE.getName(),"1000");
      }
      original();
    }
    protected void hook846() throws Exception {
      if (action.equalsIgnoreCase("evict")) {
        doAction=EVICT;
      }
 else {
        original();
      }
    }
  }
}
