package com.sleepycat.je;
public class Database {
  private Logger logger;
  /** 
 * Creates a database but does not open or fully initialize it.
 * Is protected for use in compat package.
 */
  Database(  Environment env){
    logger=envHandle.getEnvironmentImpl().getLogger();
  }
}
