package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  private Logger envLogger;
  /** 
 * Initialize the debugging logging system. Note that publishing to the
 * database log is not permitted until we've initialized the file manager in
 * recovery. We can't log safely before that.
 */
  private Logger initLogger(  File envHome) throws DatabaseException {
    return new EnvironmentImpl_initLogger(this,envHome).execute();
  }
  /** 
 * Close down the logger.
 */
  public void closeLogger(){
    Handler[] handlers=envLogger.getHandlers();
    for (int i=0; i < handlers.length; i++) {
      handlers[i].close();
    }
  }
  /** 
 * @return environment Logger, for use in debugging output.
 */
  public Logger getLogger(){
    return envLogger;
  }
  protected void hook336(  File envHome) throws DatabaseException {
    envLogger=initLogger(envHome);
    original(envHome);
  }
  protected void hook337() throws DatabaseException {
    closeLogger();
    original();
  }
@MethodObject static class EnvironmentImpl_initLogger {
    EnvironmentImpl_initLogger(    EnvironmentImpl _this,    File envHome){
      this._this=_this;
      this.envHome=envHome;
    }
    Logger execute() throws DatabaseException {
      logger=Logger.getAnonymousLogger();
      logger.setUseParentHandlers(false);
      level=Tracer.parseLevel(_this,EnvironmentParams.JE_LOGGING_LEVEL);
      logger.setLevel(level);
      return logger;
    }
    protected EnvironmentImpl _this;
    protected File envHome;
    protected Logger logger;
    protected Level level;
    protected Handler consoleHandler;
    protected Handler fileHandler;
    protected int limit;
    protected int count;
    protected String logFilePattern;
  }
}
