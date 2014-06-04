package com.sleepycat.je.config;
public class EnvironmentParams {
  public static final LongConfigParam CHECKPOINTER_WAKEUP_INTERVAL=new LongConfigParam("je.checkpointer.wakeupInterval",new Long(1000000),new Long(4294967296L),new Long(0),false,"# The checkpointer wakeup interval in microseconds. By default, this\n" + "# is inactive and we wakeup the checkpointer as a function of the\n" + "# number of bytes written to the log. (je.checkpointer.bytesInterval)");
}
