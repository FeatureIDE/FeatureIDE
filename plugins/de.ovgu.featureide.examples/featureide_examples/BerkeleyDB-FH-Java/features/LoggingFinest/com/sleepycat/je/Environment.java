package com.sleepycat.je;
public class Environment {
  protected void hook58(  String databaseName,  DatabaseConfig dbConfig) throws DatabaseException {
    Tracer.trace(Level.FINEST,environmentImpl,"Environment.open: " + " name=" + databaseName + " dbConfig="+ dbConfig);
    original(databaseName,dbConfig);
  }
}
