package com.sleepycat.je.config;
import de.ovgu.cide.jakutil.*;
/** 
 * A JE configuration parameter with an boolean value.
 */
public class BooleanConfigParam extends ConfigParam {
  private static final String DEBUG_NAME=BooleanConfigParam.class.getName();
  /** 
 * Set a boolean parameter w/default.
 * @param configName
 * @param defaultValue
 */
  BooleanConfigParam(  String configName,  boolean defaultValue,  boolean mutable,  String description){
    super(configName,Boolean.valueOf(defaultValue).toString(),mutable,description);
  }
  /** 
 * Make sure that value is a valid string for booleans.
 */
  public void validateValue(  String value) throws IllegalArgumentException {
    if (!value.trim().equalsIgnoreCase(Boolean.FALSE.toString()) && !value.trim().equalsIgnoreCase(Boolean.TRUE.toString())) {
      throw new IllegalArgumentException(DEBUG_NAME + ": " + value+ " not valid boolean "+ name);
    }
  }
}
