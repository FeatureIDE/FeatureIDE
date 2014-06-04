package com.sleepycat.je;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.util.logging.Level;
import java.util.logging.Logger;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.txn.Locker;
import com.sleepycat.je.txn.LockerFactory;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated via
 * the doc templates in the doc_src directory.
 */
public class Sequence {
  private static final byte FLAG_INCR=((byte)0x1);
  private static final byte FLAG_WRAP=((byte)0x2);
  private static final byte FLAG_OVER=((byte)0x4);
  private static final int MAX_DATA_SIZE=50;
  private static final byte CURRENT_VERSION=0;
  private Database db;
  private DatabaseEntry key;
  private boolean wrapAllowed;
  private boolean increment;
  private boolean overflow;
  private long rangeMin;
  private long rangeMax;
  private long storedValue;
  private int cacheSize;
  private long cacheValue;
  private long cacheLast;
  private TransactionConfig autoCommitConfig;
  /** 
 * Opens a sequence handle, adding the sequence record if appropriate.
 */
  Sequence(  Database db,  Transaction txn,  DatabaseEntry key,  SequenceConfig config) throws DatabaseException {
    if (db.getDatabaseImpl().getSortedDuplicates()) {
      throw new IllegalArgumentException("Sequences not supported in databases configured for " + "duplicates");
    }
    SequenceConfig useConfig=(config != null) ? config : SequenceConfig.DEFAULT;
    if (useConfig.getRangeMin() >= useConfig.getRangeMax()) {
      throw new IllegalArgumentException("Minimum sequence value must be less than the maximum");
    }
    if (useConfig.getInitialValue() > useConfig.getRangeMax() || useConfig.getInitialValue() < useConfig.getRangeMin()) {
      throw new IllegalArgumentException("Initial sequence value is out of range");
    }
    if (useConfig.getRangeMin() > useConfig.getRangeMax() - useConfig.getCacheSize()) {
      throw new IllegalArgumentException("The cache size is larger than the sequence range");
    }
    if (config.getAutoCommitNoSync()) {
      autoCommitConfig=new TransactionConfig();
      autoCommitConfig.setNoSync(true);
    }
 else {
      autoCommitConfig=null;
    }
    this.db=db;
    this.key=copyEntry(key);
    this.hook84(db);
    Locker locker=null;
    Cursor cursor=null;
    OperationStatus status=OperationStatus.NOTFOUND;
    try {
      locker=LockerFactory.getWritableLocker(db.getEnvironment(),txn,db.isTransactional(),false,autoCommitConfig);
      cursor=new Cursor(db,locker,null);
      if (useConfig.getAllowCreate()) {
        rangeMin=useConfig.getRangeMin();
        rangeMax=useConfig.getRangeMax();
        increment=!useConfig.getDecrement();
        wrapAllowed=useConfig.getWrap();
        storedValue=useConfig.getInitialValue();
        status=cursor.putNoOverwrite(key,makeData());
        if (status == OperationStatus.KEYEXIST) {
          if (useConfig.getExclusiveCreate()) {
            throw new DatabaseException("ExclusiveCreate=true and the sequence record " + "already exists.");
          }
          if (!readData(cursor,null)) {
            throw new DatabaseException("Sequence record removed during openSequence.");
          }
          status=OperationStatus.SUCCESS;
        }
      }
 else {
        if (!readData(cursor,null)) {
          throw new DatabaseException("AllowCreate=false and the sequence record " + "does not exist.");
        }
        status=OperationStatus.SUCCESS;
      }
    }
  finally {
      if (cursor != null) {
        cursor.close();
      }
      if (locker != null) {
        locker.operationEnd(status);
      }
    }
    cacheSize=useConfig.getCacheSize();
    cacheValue=storedValue;
    cacheLast=increment ? (storedValue - 1) : (storedValue + 1);
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void close() throws DatabaseException {
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 * <p>This method is synchronized to protect updating of the cached value,
 * since multiple threads may share a single handle.  Multiple handles
 * for the same database/key may be used to increase concurrency.</p>
 */
  public synchronized long get(  Transaction txn,  int delta) throws DatabaseException {
    if (delta <= 0) {
      throw new IllegalArgumentException("Sequence delta must be greater than zero");
    }
    if (rangeMin > rangeMax - delta) {
      throw new IllegalArgumentException("Sequence delta is larger than the range");
    }
    boolean cached=true;
    boolean wrapped=false;
    if ((increment && delta > ((cacheLast - cacheValue) + 1)) || (!increment && delta > ((cacheValue - cacheLast) + 1))) {
      cached=false;
      int adjust=(delta > cacheSize) ? delta : cacheSize;
      Locker locker=null;
      Cursor cursor=null;
      OperationStatus status=OperationStatus.NOTFOUND;
      try {
        locker=LockerFactory.getWritableLocker(db.getEnvironment(),txn,db.isTransactional(),false,autoCommitConfig);
        cursor=new Cursor(db,locker,null);
        readDataRequired(cursor,LockMode.RMW);
        if (overflow) {
          throw new DatabaseException("Sequence overflow " + storedValue);
        }
        BigInteger availBig;
        if (increment) {
          availBig=BigInteger.valueOf(rangeMax).subtract(BigInteger.valueOf(storedValue));
        }
 else {
          availBig=BigInteger.valueOf(storedValue).subtract(BigInteger.valueOf(rangeMin));
        }
        if (availBig.compareTo(BigInteger.valueOf(adjust)) < 0) {
          int availInt=(int)availBig.longValue();
          if (availInt < delta) {
            if (wrapAllowed) {
              storedValue=increment ? rangeMin : rangeMax;
              wrapped=true;
            }
 else {
              overflow=true;
              adjust=0;
            }
          }
 else {
            adjust=availInt;
          }
        }
        if (!increment) {
          adjust=-adjust;
        }
        storedValue+=adjust;
        cursor.put(key,makeData());
        status=OperationStatus.SUCCESS;
      }
  finally {
        if (cursor != null) {
          cursor.close();
        }
        if (locker != null) {
          locker.operationEnd(status);
        }
      }
      cacheValue=storedValue - adjust;
      cacheLast=storedValue + (increment ? (-1) : 1);
    }
    long retVal=cacheValue;
    if (increment) {
      cacheValue+=delta;
    }
 else {
      cacheValue-=delta;
    }
    this.hook83(cached);
    this.hook82(cached,wrapped,retVal);
    return retVal;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public Database getDatabase() throws DatabaseException {
    return db;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public DatabaseEntry getKey() throws DatabaseException {
    return copyEntry(key);
  }
  /** 
 * Reads persistent fields from the sequence record.
 * Throws an exception if the key is not present in the database.
 */
  private void readDataRequired(  Cursor cursor,  LockMode lockMode) throws DatabaseException {
    if (!readData(cursor,lockMode)) {
      throw new DatabaseException("The sequence record has been deleted while it is open.");
    }
  }
  /** 
 * Reads persistent fields from the sequence record.
 * Returns false if the key is not present in the database.
 */
  private boolean readData(  Cursor cursor,  LockMode lockMode) throws DatabaseException {
    DatabaseEntry data=new DatabaseEntry();
    OperationStatus status=cursor.getSearchKey(key,data,lockMode);
    if (status != OperationStatus.SUCCESS) {
      return false;
    }
    ByteBuffer buf=ByteBuffer.wrap(data.getData());
    byte ignoreVersionForNow=buf.get();
    byte flags=buf.get();
    rangeMin=LogUtils.readLong(buf);
    rangeMax=LogUtils.readLong(buf);
    storedValue=LogUtils.readLong(buf);
    increment=(flags & FLAG_INCR) != 0;
    wrapAllowed=(flags & FLAG_WRAP) != 0;
    overflow=(flags & FLAG_OVER) != 0;
    return true;
  }
  /** 
 * Makes a storable database entry from the persistent fields.
 */
  private DatabaseEntry makeData(){
    byte[] data=new byte[MAX_DATA_SIZE];
    ByteBuffer buf=ByteBuffer.wrap(data);
    byte flags=0;
    if (increment) {
      flags|=FLAG_INCR;
    }
    if (wrapAllowed) {
      flags|=FLAG_WRAP;
    }
    if (overflow) {
      flags|=FLAG_OVER;
    }
    buf.put(CURRENT_VERSION);
    buf.put(flags);
    LogUtils.writeLong(buf,rangeMin);
    LogUtils.writeLong(buf,rangeMax);
    LogUtils.writeLong(buf,storedValue);
    return new DatabaseEntry(data,0,buf.position());
  }
  /** 
 * Returns a deep copy of the given database entry.
 */
  private DatabaseEntry copyEntry(  DatabaseEntry entry){
    int len=entry.getSize();
    byte[] data;
    if (len == 0) {
      data=LogUtils.ZERO_LENGTH_BYTE_ARRAY;
    }
 else {
      data=new byte[len];
      System.arraycopy(entry.getData(),entry.getOffset(),data,0,data.length);
    }
    return new DatabaseEntry(data);
  }
  protected void hook82(  boolean cached,  boolean wrapped,  long retVal) throws DatabaseException {
  }
  protected void hook83(  boolean cached) throws DatabaseException {
  }
  protected void hook84(  Database db) throws DatabaseException {
  }
}
