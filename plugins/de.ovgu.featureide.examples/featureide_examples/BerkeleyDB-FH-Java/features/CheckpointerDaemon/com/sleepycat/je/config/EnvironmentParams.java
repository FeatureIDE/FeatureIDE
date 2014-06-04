package com.sleepycat.je.config;
public class EnvironmentParams {
  public static final IntConfigParam CHECKPOINTER_RETRY=new IntConfigParam("je.checkpointer.deadlockRetry",new Integer(0),new Integer(Integer.MAX_VALUE),new Integer(3),false,"# The number of times to retry a checkpoint if it runs into a deadlock.");
}
