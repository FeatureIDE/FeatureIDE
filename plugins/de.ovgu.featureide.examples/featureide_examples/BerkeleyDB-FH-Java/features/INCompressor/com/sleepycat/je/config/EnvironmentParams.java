package com.sleepycat.je.config;
public class EnvironmentParams {
  public static final LongConfigParam COMPRESSOR_WAKEUP_INTERVAL=new LongConfigParam("je.compressor.wakeupInterval",new Long(1000000),new Long(4294967296L),new Long(5000000),false,"# The compressor wakeup interval in microseconds.");
}
