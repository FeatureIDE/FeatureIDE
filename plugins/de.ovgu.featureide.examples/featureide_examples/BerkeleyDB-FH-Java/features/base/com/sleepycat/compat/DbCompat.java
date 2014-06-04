package com.sleepycat.compat;
import java.io.*;
import java.util.Comparator;
import com.sleepycat.je.Cursor;
import com.sleepycat.je.CursorConfig;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.Environment;
import com.sleepycat.je.EnvironmentConfig;
import com.sleepycat.je.LockMode;
import com.sleepycat.je.OperationStatus;
import com.sleepycat.je.SecondaryConfig;
import com.sleepycat.je.SecondaryCursor;
import com.sleepycat.je.SecondaryDatabase;
import com.sleepycat.je.Transaction;
import com.sleepycat.je.TransactionConfig;
import de.ovgu.cide.jakutil.*;
/** 
 * A minimal set of DB-JE compatibility methods for internal use only.
 * Two versions are maintained in parallel in the DB and JE source trees.
 * Used by the collections package.
 */
public class DbCompat {
  public static final boolean CDB=false;
  public static final boolean JOIN=true;
  public static final boolean NESTED_TRANSACTIONS=false;
  public static final boolean INSERTION_ORDERED_DUPLICATES=false;
  public static final boolean SEPARATE_DATABASE_FILES=false;
  public static final boolean MEMORY_SUBSYSTEM=false;
  public static final boolean LOCK_SUBSYSTEM=false;
  public static final boolean HASH_METHOD=false;
  public static final boolean RECNO_METHOD=false;
  public static final boolean QUEUE_METHOD=false;
  public static final boolean BTREE_RECNUM_METHOD=false;
  public static final boolean OPTIONAL_READ_UNCOMMITTED=false;
  public static final boolean SECONDARIES=true;
  public static boolean getInitializeLocking(  EnvironmentConfig config){
    return true;
  }
  public static boolean getInitializeCDB(  EnvironmentConfig config){
    return false;
  }
  public static boolean isTypeBtree(  DatabaseConfig dbConfig){
    return true;
  }
  public static boolean isTypeHash(  DatabaseConfig dbConfig){
    return false;
  }
  public static boolean isTypeQueue(  DatabaseConfig dbConfig){
    return false;
  }
  public static boolean isTypeRecno(  DatabaseConfig dbConfig){
    return false;
  }
  public static boolean getBtreeRecordNumbers(  DatabaseConfig dbConfig){
    return false;
  }
  public static boolean getReadUncommitted(  DatabaseConfig dbConfig){
    return true;
  }
  public static boolean getRenumbering(  DatabaseConfig dbConfig){
    return false;
  }
  public static boolean getSortedDuplicates(  DatabaseConfig dbConfig){
    return dbConfig.getSortedDuplicates();
  }
  public static boolean getUnsortedDuplicates(  DatabaseConfig dbConfig){
    return false;
  }
  public static CursorConfig cloneCursorConfig(  CursorConfig config){
    CursorConfig newConfig=new CursorConfig();
    newConfig.setReadCommitted(config.getReadCommitted());
    newConfig.setReadUncommitted(config.getReadUncommitted());
    return newConfig;
  }
  public static boolean getWriteCursor(  CursorConfig config){
    return false;
  }
  public static void setWriteCursor(  CursorConfig config,  boolean write){
    if (write) {
      throw new UnsupportedOperationException();
    }
  }
  public static void setRecordNumber(  DatabaseEntry entry,  int recNum){
    throw new UnsupportedOperationException();
  }
  public static int getRecordNumber(  DatabaseEntry entry){
    throw new UnsupportedOperationException();
  }
  public static String getDatabaseFile(  Database db) throws DatabaseException {
    return null;
  }
  public static OperationStatus getCurrentRecordNumber(  Cursor cursor,  DatabaseEntry key,  LockMode lockMode) throws DatabaseException {
    throw new UnsupportedOperationException();
  }
  public static OperationStatus getSearchRecordNumber(  Cursor cursor,  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    throw new UnsupportedOperationException();
  }
  public static OperationStatus getSearchRecordNumber(  SecondaryCursor cursor,  DatabaseEntry key,  DatabaseEntry pKey,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    throw new UnsupportedOperationException();
  }
  public static OperationStatus putAfter(  Cursor cursor,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    throw new UnsupportedOperationException();
  }
  public static OperationStatus putBefore(  Cursor cursor,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    throw new UnsupportedOperationException();
  }
  public static OperationStatus append(  Database db,  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    throw new UnsupportedOperationException();
  }
  public static Transaction getThreadTransaction(  Environment env) throws DatabaseException {
    return env.getThreadTransaction();
  }
  public static void setInitializeCache(  EnvironmentConfig config,  boolean val){
    if (!val) {
      throw new UnsupportedOperationException();
    }
  }
  public static void setInitializeLocking(  EnvironmentConfig config,  boolean val){
    if (!val) {
      throw new UnsupportedOperationException();
    }
  }
  public static void setInitializeCDB(  EnvironmentConfig config,  boolean val){
    if (val) {
      throw new UnsupportedOperationException();
    }
  }
  public static void setLockDetectModeOldest(  EnvironmentConfig config){
  }
  public static void setSerializableIsolation(  TransactionConfig config,  boolean val){
    config.setSerializableIsolation(val);
  }
  public static void setBtreeComparator(  DatabaseConfig dbConfig,  Comparator comparator){
    dbConfig.setBtreeComparator(comparator.getClass());
  }
  public static void setTypeBtree(  DatabaseConfig dbConfig){
  }
  public static void setTypeHash(  DatabaseConfig dbConfig){
    throw new UnsupportedOperationException();
  }
  public static void setTypeRecno(  DatabaseConfig dbConfig){
    throw new UnsupportedOperationException();
  }
  public static void setTypeQueue(  DatabaseConfig dbConfig){
    throw new UnsupportedOperationException();
  }
  public static void setBtreeRecordNumbers(  DatabaseConfig dbConfig,  boolean val){
    throw new UnsupportedOperationException();
  }
  public static void setReadUncommitted(  DatabaseConfig dbConfig,  boolean val){
  }
  public static void setRenumbering(  DatabaseConfig dbConfig,  boolean val){
    throw new UnsupportedOperationException();
  }
  public static void setSortedDuplicates(  DatabaseConfig dbConfig,  boolean val){
    dbConfig.setSortedDuplicates(val);
  }
  public static void setUnsortedDuplicates(  DatabaseConfig dbConfig,  boolean val){
    if (val) {
      throw new UnsupportedOperationException();
    }
  }
  public static void setRecordLength(  DatabaseConfig dbConfig,  int val){
    if (val != 0) {
      throw new UnsupportedOperationException();
    }
  }
  public static void setRecordPad(  DatabaseConfig dbConfig,  int val){
    throw new UnsupportedOperationException();
  }
  public static Database openDatabase(  Environment env,  Transaction txn,  String file,  String name,  DatabaseConfig config) throws DatabaseException, FileNotFoundException {
    return env.openDatabase(txn,makeDbName(file,name),config);
  }
  public static SecondaryDatabase openSecondaryDatabase(  Environment env,  Transaction txn,  String file,  String name,  Database primary,  SecondaryConfig config) throws DatabaseException, FileNotFoundException {
    return env.openSecondaryDatabase(txn,makeDbName(file,name),primary,config);
  }
  private static String makeDbName(  String file,  String name){
    if (file == null) {
      return name;
    }
 else {
      if (name != null) {
        return file + '.' + name;
      }
 else {
        return file;
      }
    }
  }
}
