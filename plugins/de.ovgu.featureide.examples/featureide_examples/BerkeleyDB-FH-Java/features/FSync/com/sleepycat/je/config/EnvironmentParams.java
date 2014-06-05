package com.sleepycat.je.config;
public class EnvironmentParams {
  public static final LongConfigParam LOG_FSYNC_TIMEOUT=new LongConfigParam("je.log.fsyncTimeout",new Long(10000L),null,new Long(500000L),false,"# Timeout limit for group file sync, in microseconds.");
}
