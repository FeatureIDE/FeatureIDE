package com.sleepycat.je.config;
public class EnvironmentParams {
  public static final IntConfigParam EVICTOR_RETRY=new IntConfigParam("je.evictor.deadlockRetry",new Integer(0),new Integer(Integer.MAX_VALUE),new Integer(3),false,"# The number of times to retry the evictor if it runs into a deadlock.");
}
