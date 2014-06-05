package com.sleepycat.je;
public class Environment {
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public boolean verify(  VerifyConfig config,  PrintStream out) throws DatabaseException {
    checkHandleIsValid();
    checkEnv();
    VerifyConfig useConfig=(config == null) ? VerifyConfig.DEFAULT : config;
    return environmentImpl.verify(useConfig,out);
  }
}
