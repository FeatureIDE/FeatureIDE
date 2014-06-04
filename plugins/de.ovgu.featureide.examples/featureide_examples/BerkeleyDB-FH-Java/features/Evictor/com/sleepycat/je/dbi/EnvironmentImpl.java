package com.sleepycat.je.dbi;
import com.sleepycat.je.evictor.Evictor;
public class EnvironmentImpl {
  private Evictor evictor;
  public void invokeEvictor() throws DatabaseException {
    if (evictor != null) {
      evictor.doEvict(Evictor.SOURCE_MANUAL);
    }
  }
  public void shutdownEvictor() throws InterruptedException {
    if (evictor != null) {
      evictor.shutdown();
      evictor.clearEnv();
      evictor=null;
    }
    return;
  }
  public Evictor getEvictor(){
    return evictor;
  }
  void alertEvictor(){
    if (evictor != null) {
      evictor.alert();
    }
  }
  protected void hook334(){
    if (evictor != null) {
      evictor.requestShutdown();
    }
    original();
  }
  /** 
 * Ask all daemon threads to shut down.
 */
  private void shutdownDaemons() throws InterruptedException {
    original();
    shutdownEvictor();
  }
@MethodObject static class EnvironmentImpl_createDaemons {
    void execute() throws DatabaseException {
      _this.evictor=new Evictor(_this,"Evictor");
      original();
    }
  }
}
