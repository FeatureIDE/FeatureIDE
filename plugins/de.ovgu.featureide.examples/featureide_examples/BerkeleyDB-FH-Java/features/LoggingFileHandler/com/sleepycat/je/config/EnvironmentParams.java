package com.sleepycat.je.config;
public class EnvironmentParams {
  public static final BooleanConfigParam JE_LOGGING_FILE=new BooleanConfigParam("java.util.logging.FileHandler.on",true,false,"# Use FileHandler in logging system.");
  public static final IntConfigParam JE_LOGGING_FILE_LIMIT=new IntConfigParam("java.util.logging.FileHandler.limit",new Integer(1000),new Integer(1000000000),new Integer(10000000),false,"# Log file limit for FileHandler.");
  public static final IntConfigParam JE_LOGGING_FILE_COUNT=new IntConfigParam("java.util.logging.FileHandler.count",new Integer(1),null,new Integer(10),false,"# Log file count for FileHandler.");
}
