package com.sleepycat.je.config;
public class EnvironmentParams {
  public static final LongConfigParam CHECKPOINTER_BYTES_INTERVAL=new LongConfigParam("je.checkpointer.bytesInterval",new Long(0),new Long(Long.MAX_VALUE),new Long(20000000),false,"# Ask the checkpointer to run every time we write this many bytes\n" + "# to the log. If set, supercedes je.checkpointer.wakeupInterval. To\n" + "# use time based checkpointing, set this to 0.");
}
