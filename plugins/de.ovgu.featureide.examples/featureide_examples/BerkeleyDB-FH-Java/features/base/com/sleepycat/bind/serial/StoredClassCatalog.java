package com.sleepycat.bind.serial;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamClass;
import java.io.Serializable;
import java.math.BigInteger;
import java.util.HashMap;
import com.sleepycat.compat.DbCompat;
import com.sleepycat.je.Cursor;
import com.sleepycat.je.CursorConfig;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.EnvironmentConfig;
import com.sleepycat.je.LockMode;
import com.sleepycat.je.OperationStatus;
import com.sleepycat.util.RuntimeExceptionWrapper;
import com.sleepycat.util.UtfOps;
import de.ovgu.cide.jakutil.*;
/** 
 * A <code>ClassCatalog</code> that is stored in a <code>Database</code>.
 * <p>
 * A single <code>StoredClassCatalog</code> object is normally used along with
 * a set of databases that stored serialized objects.
 * </p>
 * @author Mark Hayes
 */
public class StoredClassCatalog implements ClassCatalog {
  private static final byte REC_LAST_CLASS_ID=(byte)0;
  private static final byte REC_CLASS_FORMAT=(byte)1;
  private static final byte REC_CLASS_INFO=(byte)2;
  private static final byte[] LAST_CLASS_ID_KEY={REC_LAST_CLASS_ID};
  private Database db;
  private HashMap classMap;
  private HashMap formatMap;
  private LockMode writeLockMode;
  private boolean cdbMode;
  /** 
 * Creates a catalog based on a given database. To save resources, only a
 * single catalog object should be used for each unique catalog database.
 * @param databasean open database to use as the class catalog. It must be a
 * BTREE database and must not allow duplicates.
 * @throws DatabaseExceptionif an error occurs accessing the database.
 * @throws IllegalArgumentExceptionif the database is not a BTREE database or if it configured
 * to allow duplicates.
 */
  public StoredClassCatalog(  Database database) throws DatabaseException, IllegalArgumentException {
    db=database;
    DatabaseConfig dbConfig=db.getConfig();
    EnvironmentConfig envConfig=db.getEnvironment().getConfig();
    writeLockMode=hook_getLockMode(envConfig);
    cdbMode=DbCompat.getInitializeCDB(envConfig);
    if (!DbCompat.isTypeBtree(dbConfig)) {
      throw new IllegalArgumentException("The class catalog must be a BTREE database.");
    }
    if (DbCompat.getSortedDuplicates(dbConfig) || DbCompat.getUnsortedDuplicates(dbConfig)) {
      throw new IllegalArgumentException("The class catalog database must not allow duplicates.");
    }
    classMap=new HashMap();
    formatMap=new HashMap();
    DatabaseEntry key=new DatabaseEntry(LAST_CLASS_ID_KEY);
    DatabaseEntry data=new DatabaseEntry();
    if (dbConfig.getReadOnly()) {
      OperationStatus status=db.get(null,key,data,null);
      if (status != OperationStatus.SUCCESS) {
        throw new IllegalStateException("A read-only catalog database may not be empty");
      }
    }
 else {
      data.setData(new byte[1]);
      db.putNoOverwrite(null,key,data);
    }
  }
  private LockMode hook_getLockMode(  EnvironmentConfig envConfig) throws DatabaseException {
    return (DbCompat.getInitializeLocking(envConfig)) ? LockMode.RMW : LockMode.DEFAULT;
  }
  public synchronized void close() throws DatabaseException {
    if (db != null) {
      db.close();
    }
    db=null;
    formatMap=null;
    classMap=null;
  }
  public synchronized byte[] getClassID(  ObjectStreamClass classFormat) throws DatabaseException, ClassNotFoundException {
    ClassInfo classInfo=getClassInfo(classFormat);
    return classInfo.getClassID();
  }
  public synchronized ObjectStreamClass getClassFormat(  byte[] classID) throws DatabaseException, ClassNotFoundException {
    return getClassFormat(classID,new DatabaseEntry());
  }
  /** 
 * Internal function for getting the class format. Allows passing the
 * DatabaseEntry object for the data, so the bytes of the class format can
 * be examined afterwards.
 */
  private ObjectStreamClass getClassFormat(  byte[] classID,  DatabaseEntry data) throws DatabaseException, ClassNotFoundException {
    BigInteger classIDObj=new BigInteger(classID);
    ObjectStreamClass classFormat=(ObjectStreamClass)formatMap.get(classIDObj);
    if (classFormat == null) {
      byte[] keyBytes=new byte[classID.length + 1];
      keyBytes[0]=REC_CLASS_FORMAT;
      System.arraycopy(classID,0,keyBytes,1,classID.length);
      DatabaseEntry key=new DatabaseEntry(keyBytes);
      OperationStatus status=db.get(null,key,data,LockMode.DEFAULT);
      if (status != OperationStatus.SUCCESS) {
        throw new ClassNotFoundException("Catalog class ID not found");
      }
      try {
        ObjectInputStream ois=new ObjectInputStream(new ByteArrayInputStream(data.getData(),data.getOffset(),data.getSize()));
        classFormat=(ObjectStreamClass)ois.readObject();
      }
 catch (      IOException e) {
        throw new RuntimeExceptionWrapper(e);
      }
      formatMap.put(classIDObj,classFormat);
    }
    return classFormat;
  }
  /** 
 * Get the ClassInfo for a given class name, adding it and its
 * ObjectStreamClass to the database if they are not already present, and
 * caching both of them using the class info and class format maps. When a
 * class is first loaded from the database, the stored ObjectStreamClass is
 * compared to the current ObjectStreamClass loaded by the Java class
 * loader; if they are different, a new class ID is assigned for the current
 * format.
 */
  private ClassInfo getClassInfo(  ObjectStreamClass classFormat) throws DatabaseException, ClassNotFoundException {
    String className=classFormat.getName();
    ClassInfo classInfo=(ClassInfo)classMap.get(className);
    if (classInfo != null) {
      return classInfo;
    }
 else {
      char[] nameChars=className.toCharArray();
      byte[] keyBytes=new byte[1 + UtfOps.getByteLength(nameChars)];
      keyBytes[0]=REC_CLASS_INFO;
      UtfOps.charsToBytes(nameChars,0,keyBytes,1,nameChars.length);
      DatabaseEntry key=new DatabaseEntry(keyBytes);
      DatabaseEntry data=new DatabaseEntry();
      OperationStatus status=db.get(null,key,data,LockMode.DEFAULT);
      if (status != OperationStatus.SUCCESS) {
        classInfo=putClassInfo(new ClassInfo(),className,key,classFormat);
      }
 else {
        classInfo=new ClassInfo(data);
        DatabaseEntry formatData=new DatabaseEntry();
        ObjectStreamClass storedClassFormat=getClassFormat(classInfo.getClassID(),formatData);
        if (!areClassFormatsEqual(storedClassFormat,getBytes(formatData),classFormat)) {
          classInfo=putClassInfo(classInfo,className,key,classFormat);
        }
        classInfo.setClassFormat(classFormat);
        classMap.put(className,classInfo);
      }
    }
    return classInfo;
  }
  /** 
 * Assign a new class ID (increment the current ID record), write the
 * ObjectStreamClass record for this new ID, and update the ClassInfo record
 * with the new ID also. The ClassInfo passed as an argument is the one to
 * be updated.
 */
  private ClassInfo putClassInfo(  ClassInfo classInfo,  String className,  DatabaseEntry classKey,  ObjectStreamClass classFormat) throws DatabaseException, ClassNotFoundException {
    CursorConfig cursorConfig=null;
    if (cdbMode) {
      cursorConfig=new CursorConfig();
      DbCompat.setWriteCursor(cursorConfig,true);
    }
    Cursor cursor=null;
    try {
      cursor=db.openCursor(null,cursorConfig);
      DatabaseEntry key=new DatabaseEntry(LAST_CLASS_ID_KEY);
      DatabaseEntry data=new DatabaseEntry();
      OperationStatus status=cursor.getSearchKey(key,data,writeLockMode);
      if (status != OperationStatus.SUCCESS) {
        throw new IllegalStateException("Class ID not initialized");
      }
      byte[] idBytes=getBytes(data);
      idBytes=incrementID(idBytes);
      data.setData(idBytes);
      cursor.put(key,data);
      byte[] keyBytes=new byte[1 + idBytes.length];
      keyBytes[0]=REC_CLASS_FORMAT;
      System.arraycopy(idBytes,0,keyBytes,1,idBytes.length);
      key.setData(keyBytes);
      ByteArrayOutputStream baos=new ByteArrayOutputStream();
      ObjectOutputStream oos;
      try {
        oos=new ObjectOutputStream(baos);
        oos.writeObject(classFormat);
      }
 catch (      IOException e) {
        throw new RuntimeExceptionWrapper(e);
      }
      data.setData(baos.toByteArray());
      cursor.put(key,data);
      classInfo.setClassID(idBytes);
      classInfo.toDbt(data);
      cursor.put(classKey,data);
      classInfo.setClassFormat(classFormat);
      classMap.put(className,classInfo);
      formatMap.put(new BigInteger(idBytes),classFormat);
      return classInfo;
    }
  finally {
      if (cursor != null) {
        cursor.close();
      }
      hook_commitTransaction();
    }
  }
  private void hook_commitTransaction() throws DatabaseException {
  }
  private static byte[] incrementID(  byte[] key){
    BigInteger id=new BigInteger(key);
    id=id.add(BigInteger.valueOf(1));
    return id.toByteArray();
  }
  /** 
 * Holds the class format key for a class, maintains a reference to the
 * ObjectStreamClass. Other fields can be added when we need to store more
 * information per class.
 */
private static class ClassInfo implements Serializable {
    private byte[] classID;
    private transient ObjectStreamClass classFormat;
    ClassInfo(){
    }
    ClassInfo(    DatabaseEntry dbt){
      byte[] data=dbt.getData();
      int len=data[0];
      classID=new byte[len];
      System.arraycopy(data,1,classID,0,len);
    }
    void toDbt(    DatabaseEntry dbt){
      byte[] data=new byte[1 + classID.length];
      data[0]=(byte)classID.length;
      System.arraycopy(classID,0,data,1,classID.length);
      dbt.setData(data);
    }
    void setClassID(    byte[] classID){
      this.classID=classID;
    }
    byte[] getClassID(){
      return classID;
    }
    ObjectStreamClass getClassFormat(){
      return classFormat;
    }
    void setClassFormat(    ObjectStreamClass classFormat){
      this.classFormat=classFormat;
    }
  }
  /** 
 * Return whether two class formats are equal. This determines whether a new
 * class format is needed for an object being serialized. Formats must be
 * identical in all respects, or a new format is needed.
 */
  private static boolean areClassFormatsEqual(  ObjectStreamClass format1,  byte[] format1Bytes,  ObjectStreamClass format2){
    try {
      if (format1Bytes == null) {
        format1Bytes=getObjectBytes(format1);
      }
      byte[] format2Bytes=getObjectBytes(format2);
      return java.util.Arrays.equals(format2Bytes,format1Bytes);
    }
 catch (    IOException e) {
      return false;
    }
  }
  private static byte[] ZERO_LENGTH_BYTE_ARRAY=new byte[0];
  private static byte[] getBytes(  DatabaseEntry dbt){
    byte[] b=dbt.getData();
    if (b == null) {
      return null;
    }
    if (dbt.getOffset() == 0 && b.length == dbt.getSize()) {
      return b;
    }
    int len=dbt.getSize();
    if (len == 0) {
      return ZERO_LENGTH_BYTE_ARRAY;
    }
 else {
      byte[] t=new byte[len];
      System.arraycopy(b,dbt.getOffset(),t,0,t.length);
      return t;
    }
  }
  private static byte[] getObjectBytes(  Object o) throws IOException {
    ByteArrayOutputStream baos=new ByteArrayOutputStream();
    ObjectOutputStream oos=new ObjectOutputStream(baos);
    oos.writeObject(o);
    return baos.toByteArray();
  }
}
