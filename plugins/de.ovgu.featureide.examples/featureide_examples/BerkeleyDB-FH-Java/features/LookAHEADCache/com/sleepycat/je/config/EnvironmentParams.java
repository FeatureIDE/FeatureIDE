package com.sleepycat.je.config;
public class EnvironmentParams {
  public static final IntConfigParam CLEANER_LOOK_AHEAD_CACHE_SIZE=new IntConfigParam("je.cleaner.lookAheadCacheSize",new Integer(0),null,new Integer(8192),true,"# The look ahead cache size for cleaning in bytes.  Increasing this\n" + "# value can reduce the number of Btree lookups.");
}
