package com.sleepycat.je.config;
public class EnvironmentParams {
  public static final BooleanConfigParam LOG_CHECKSUM_READ=new BooleanConfigParam("je.log.checksumRead",true,false,"# If true, perform a checksum check when reading entries from log.");
}
