package com.sleepycat.je.dbi;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.EnvironmentConfig;
import com.sleepycat.je.config.BooleanConfigParam;
import com.sleepycat.je.config.ConfigParam;
import com.sleepycat.je.config.IntConfigParam;
import com.sleepycat.je.config.LongConfigParam;
import com.sleepycat.je.config.ShortConfigParam;
import de.ovgu.cide.jakutil.*;
/** 
 * DbConfigManager holds the configuration parameters for an environment.
 */
public class DbConfigManager {
  private EnvironmentConfig environmentConfig;
  /** 
 * Todo: should this even be a separate class? 
 */
  public DbConfigManager(  EnvironmentConfig config) throws DbConfigException {
    environmentConfig=config;
  }
  public EnvironmentConfig getEnvironmentConfig(){
    return environmentConfig;
  }
  /** 
 * Get this parameter from the environment wide configuration settings.
 * @param configParam
 * @return default for param if param wasn't explicitly set
 */
  public synchronized String get(  ConfigParam configParam) throws IllegalArgumentException {
    return environmentConfig.getConfigParam(configParam.getName());
  }
  /** 
 * Get this parameter from the environment wide configuration settings.
 * @param configParam
 * @return default for param if param wasn't explicitly set
 */
  public synchronized String get(  String configParamName) throws IllegalArgumentException {
    return environmentConfig.getConfigParam(configParamName);
  }
  /** 
 * Get this parameter from the environment wide configuration settings.
 * @param configParam
 * @return default for param if it wasn't explicitly set.
 */
  public boolean getBoolean(  BooleanConfigParam configParam) throws DatabaseException {
    String val=get(configParam);
    return Boolean.valueOf(val).booleanValue();
  }
  /** 
 * Get this parameter from the environment wide configuration settings.
 * @param configParam
 * @return default for param if it wasn't explicitly set.
 */
  public short getShort(  ShortConfigParam configParam) throws DatabaseException {
    String val=get(configParam);
    short shortValue=0;
    try {
      shortValue=Short.parseShort(val);
    }
 catch (    NumberFormatException e) {
      assert false : e.getMessage();
    }
    return shortValue;
  }
  /** 
 * Get this parameter from the environment wide configuration settings.
 * @param configParam
 * @return default for param if it wasn't explicitly set.
 */
  public int getInt(  IntConfigParam configParam) throws DatabaseException {
    String val=get(configParam);
    int intValue=0;
    if (val != null) {
      try {
        intValue=Integer.parseInt(val);
      }
 catch (      NumberFormatException e) {
        assert false : e.getMessage();
      }
    }
    return intValue;
  }
  /** 
 * Get this parameter from the environment wide configuration settings.
 * @param configParam
 * @return default for param if it wasn't explicitly set
 */
  public long getLong(  LongConfigParam configParam) throws DatabaseException {
    String val=get(configParam);
    long longValue=0;
    if (val != null) {
      try {
        longValue=Long.parseLong(val);
      }
 catch (      NumberFormatException e) {
        assert false : e.getMessage();
      }
    }
    return longValue;
  }
}
