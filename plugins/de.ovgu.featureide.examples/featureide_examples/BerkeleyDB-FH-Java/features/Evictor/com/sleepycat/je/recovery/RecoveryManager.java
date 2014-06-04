package com.sleepycat.je.recovery;
public class RecoveryManager {
  protected void hook596() throws IOException, DatabaseException {
    env.invokeEvictor();
    original();
  }
  protected void hook597() throws IOException, DatabaseException, Exception {
    env.invokeEvictor();
    original();
  }
  protected void hook598() throws IOException, DatabaseException, Exception {
    env.invokeEvictor();
    original();
  }
}
