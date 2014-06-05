package com.sleepycat.je;
import de.ovgu.cide.jakutil.*;
/** 
 * Utils for use in the db package.
 */
class DatabaseUtil {
  /** 
 * Throw an exception if the parameter is null.
 */
  static void checkForNullParam(  Object param,  String name){
    if (param == null) {
      throw new NullPointerException(name + " cannot be null");
    }
  }
  /** 
 * Throw an exception if the dbt is null or the data field is not set.
 */
  static void checkForNullDbt(  DatabaseEntry dbt,  String name,  boolean checkData){
    if (dbt == null) {
      throw new NullPointerException("DatabaseEntry " + name + " cannot be null");
    }
    if (checkData) {
      if (dbt.getData() == null) {
        throw new NullPointerException("Data field for DatabaseEntry " + name + " cannot be null");
      }
    }
  }
  /** 
 * Throw an exception if the key dbt has the partial flag set.  This method
 * should be called for all put() operations.
 */
  static void checkForPartialKey(  DatabaseEntry dbt){
    if (dbt.getPartial()) {
      throw new IllegalArgumentException("A partial key DatabaseEntry is not allowed");
    }
  }
}
