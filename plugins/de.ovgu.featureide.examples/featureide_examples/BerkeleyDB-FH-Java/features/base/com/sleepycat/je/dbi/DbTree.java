package com.sleepycat.je.dbi;
import java.io.PrintStream;
import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DatabaseNotFoundException;
import com.sleepycat.je.DeadlockException;
import com.sleepycat.je.OperationStatus;
import com.sleepycat.je.TransactionConfig;
import com.sleepycat.je.dbi.CursorImpl.SearchMode;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogException;
import com.sleepycat.je.log.LogReadable;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LoggableObject;
import com.sleepycat.je.tree.ChildReference;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.LN;
import com.sleepycat.je.tree.MapLN;
import com.sleepycat.je.tree.NameLN;
import com.sleepycat.je.tree.Tree;
import com.sleepycat.je.tree.TreeUtils;
import com.sleepycat.je.tree.WithRootLatched;
import com.sleepycat.je.txn.AutoTxn;
import com.sleepycat.je.txn.BasicLocker;
import com.sleepycat.je.txn.LockType;
import com.sleepycat.je.txn.Locker;
import de.ovgu.cide.jakutil.*;
/** 
 * Represents the DatabaseImpl Naming Tree.
 */
public class DbTree implements LoggableObject, LogReadable {
  public static final DatabaseId ID_DB_ID=new DatabaseId(0);
  public static final DatabaseId NAME_DB_ID=new DatabaseId(1);
  public static final String ID_DB_NAME="_jeIdMap";
  public static final String NAME_DB_NAME="_jeNameMap";
  public static final String UTILIZATION_DB_NAME="_jeUtilization";
  private static final String[] RESERVED_DB_NAMES={ID_DB_NAME,NAME_DB_NAME,UTILIZATION_DB_NAME};
  private int lastAllocatedDbId;
  private DatabaseImpl idDatabase;
  private DatabaseImpl nameDatabase;
  private EnvironmentImpl envImpl;
  /** 
 * Create a dbTree from the log.
 */
  public DbTree() throws DatabaseException {
    this.envImpl=null;
    idDatabase=new DatabaseImpl();
    idDatabase.setDebugDatabaseName(ID_DB_NAME);
    nameDatabase=new DatabaseImpl();
    nameDatabase.setDebugDatabaseName(NAME_DB_NAME);
  }
  /** 
 * Create a new dbTree for a new environment.
 */
  public DbTree(  EnvironmentImpl env) throws DatabaseException {
    this.envImpl=env;
    idDatabase=new DatabaseImpl(ID_DB_NAME,new DatabaseId(0),env,new DatabaseConfig());
    nameDatabase=new DatabaseImpl(NAME_DB_NAME,new DatabaseId(1),env,new DatabaseConfig());
    lastAllocatedDbId=1;
  }
  /** 
 * Get the latest allocated id, for checkpoint info.
 */
  public synchronized int getLastDbId(){
    return lastAllocatedDbId;
  }
  /** 
 * Get the next available database id.
 */
  private synchronized int getNextDbId(){
    return ++lastAllocatedDbId;
  }
  /** 
 * Initialize the db id, from recovery.
 */
  public synchronized void setLastDbId(  int maxDbId){
    lastAllocatedDbId=maxDbId;
  }
  private Locker createLocker(  EnvironmentImpl envImpl) throws DatabaseException {
    if (envImpl.isNoLocking()) {
      return new BasicLocker(envImpl);
    }
 else {
      return new AutoTxn(envImpl,new TransactionConfig());
    }
  }
  /** 
 * Set the db environment during recovery, after instantiating the tree from
 * the log.
 */
  void setEnvironmentImpl(  EnvironmentImpl envImpl) throws DatabaseException {
    this.envImpl=envImpl;
    idDatabase.setEnvironmentImpl(envImpl);
    nameDatabase.setEnvironmentImpl(envImpl);
  }
  /** 
 * Create a database.
 */
  public synchronized DatabaseImpl createDb(  Locker locker,  String databaseName,  DatabaseConfig dbConfig,  Database databaseHandle) throws DatabaseException {
    return createDb(locker,databaseName,dbConfig,databaseHandle,true);
  }
  /** 
 * Create a database.
 * @param lockerowning locker
 * @param databaseNameidentifier for database
 * @param dbConfig
 * @param allowEvictionis whether eviction is allowed during cursor operations.
 */
  public synchronized DatabaseImpl createDb(  Locker locker,  String databaseName,  DatabaseConfig dbConfig,  Database databaseHandle,  boolean allowEviction) throws DatabaseException {
    DatabaseId newId=new DatabaseId(getNextDbId());
    DatabaseImpl newDb=new DatabaseImpl(databaseName,newId,envImpl,dbConfig);
    CursorImpl idCursor=null;
    CursorImpl nameCursor=null;
    boolean operationOk=false;
    Locker autoTxn=null;
    try {
      nameCursor=new CursorImpl(nameDatabase,locker);
      this.hook307(allowEviction,nameCursor);
      LN nameLN=new NameLN(newId);
      nameCursor.putLN(databaseName.getBytes("UTF-8"),nameLN,false);
      if (databaseHandle != null) {
        locker.addToHandleMaps(new Long(nameLN.getNodeId()),databaseHandle);
      }
      autoTxn=createLocker(envImpl);
      idCursor=new CursorImpl(idDatabase,autoTxn);
      this.hook306(allowEviction,idCursor);
      idCursor.putLN(newId.getBytes(),new MapLN(newDb),false);
      operationOk=true;
    }
 catch (    UnsupportedEncodingException UEE) {
      throw new DatabaseException(UEE);
    }
 finally {
      if (idCursor != null) {
        idCursor.close();
      }
      if (nameCursor != null) {
        nameCursor.close();
      }
      if (autoTxn != null) {
        autoTxn.operationEnd(operationOk);
      }
    }
    return newDb;
  }
  /** 
 * Called by the Tree to propagate a root change. If the tree is a data
 * database, we will write the MapLn that represents this db to the log. If
 * the tree is one of the mapping dbs, we'll write the dbtree to the log.
 * @param dbthe target db
 */
  public void modifyDbRoot(  DatabaseImpl db) throws DatabaseException {
    if (db.getId().equals(ID_DB_ID) || db.getId().equals(NAME_DB_ID)) {
      envImpl.logMapTreeRoot();
    }
 else {
      Locker locker=createLocker(envImpl);
      CursorImpl cursor=new CursorImpl(idDatabase,locker);
      boolean operationOk=false;
      try {
        DatabaseEntry keyDbt=new DatabaseEntry(db.getId().getBytes());
        MapLN mapLN=null;
        while (true) {
          try {
            boolean searchOk=(cursor.searchAndPosition(keyDbt,new DatabaseEntry(),SearchMode.SET,LockType.WRITE) & CursorImpl.FOUND) != 0;
            if (!searchOk) {
              throw new DatabaseException("can't find database " + db.getId());
            }
            mapLN=(MapLN)cursor.getCurrentLNAlreadyLatched(LockType.WRITE);
            assert mapLN != null;
          }
 catch (          DeadlockException DE) {
            cursor.close();
            locker.operationEnd(false);
            locker=createLocker(envImpl);
            cursor=new CursorImpl(idDatabase,locker);
            continue;
          }
 finally {
            this.hook299(cursor);
          }
          break;
        }
        RewriteMapLN writeMapLN=new RewriteMapLN(cursor);
        mapLN.getDatabase().getTree().withRootLatchedExclusive(writeMapLN);
        operationOk=true;
      }
  finally {
        if (cursor != null) {
          cursor.close();
        }
        locker.operationEnd(operationOk);
      }
    }
  }
private static class RewriteMapLN implements WithRootLatched {
    private CursorImpl cursor;
    RewriteMapLN(    CursorImpl cursor){
      this.cursor=cursor;
    }
    public IN doWork(    ChildReference root) throws DatabaseException {
      DatabaseEntry dataDbt=new DatabaseEntry(new byte[0]);
      cursor.putCurrent(dataDbt,null,null);
      return null;
    }
  }
  private NameLockResult lockNameLN(  Locker locker,  String databaseName,  String action) throws DatabaseException {
    NameLockResult result=new NameLockResult();
    result.dbImpl=getDb(locker,databaseName,null);
    if (result.dbImpl == null) {
      throw new DatabaseNotFoundException("Attempted to " + action + " non-existent database "+ databaseName);
    }
    result.nameCursor=new CursorImpl(nameDatabase,locker);
    try {
      DatabaseEntry key=new DatabaseEntry(databaseName.getBytes("UTF-8"));
      boolean found=(result.nameCursor.searchAndPosition(key,null,SearchMode.SET,LockType.WRITE) & CursorImpl.FOUND) != 0;
      if (!found) {
        this.hook300(result);
        result.nameCursor.close();
        result.nameCursor=null;
        return result;
      }
      result.nameLN=(NameLN)result.nameCursor.getCurrentLNAlreadyLatched(LockType.WRITE);
      assert result.nameLN != null;
      int handleCount=result.dbImpl.getReferringHandleCount();
      if (handleCount > 0) {
        throw new DatabaseException("Can't " + action + " database "+ databaseName+ ","+ handleCount+ " open Dbs exist");
      }
    }
 catch (    UnsupportedEncodingException UEE) {
      this.hook301(result);
      result.nameCursor.close();
      throw new DatabaseException(UEE);
    }
catch (    DatabaseException e) {
      this.hook302(result);
      result.nameCursor.close();
      throw e;
    }
    return result;
  }
private static class NameLockResult {
    CursorImpl nameCursor;
    DatabaseImpl dbImpl;
    NameLN nameLN;
  }
  void deleteMapLN(  DatabaseId id) throws DatabaseException {
    Locker autoTxn=null;
    boolean operationOk=false;
    CursorImpl idCursor=null;
    try {
      autoTxn=createLocker(envImpl);
      idCursor=new CursorImpl(idDatabase,autoTxn);
      boolean found=(idCursor.searchAndPosition(new DatabaseEntry(id.getBytes()),null,SearchMode.SET,LockType.WRITE) & CursorImpl.FOUND) != 0;
      if (found) {
        idCursor.delete();
      }
      operationOk=true;
    }
  finally {
      if (idCursor != null) {
        idCursor.close();
      }
      if (autoTxn != null) {
        autoTxn.operationEnd(operationOk);
      }
    }
  }
  /** 
 * Get a database object given a database name.
 */
  public DatabaseImpl getDb(  Locker nameLocker,  String databaseName,  Database databaseHandle) throws DatabaseException {
    return getDb(nameLocker,databaseName,databaseHandle,true);
  }
  /** 
 * Get a database object given a database name.
 * @param nameLockeris used to access the NameLN. As always, a NullTxn is used to
 * access the MapLN.
 * @param databaseNametarget database
 * @return null if database doesn't exist
 * @param allowEvictionis whether eviction is allowed during cursor operations.
 */
  public DatabaseImpl getDb(  Locker nameLocker,  String databaseName,  Database databaseHandle,  boolean allowEviction) throws DatabaseException {
    try {
      CursorImpl nameCursor=null;
      DatabaseId id=null;
      try {
        nameCursor=new CursorImpl(nameDatabase,nameLocker);
        this.hook308(allowEviction,nameCursor);
        DatabaseEntry keyDbt=new DatabaseEntry(databaseName.getBytes("UTF-8"));
        boolean found=(nameCursor.searchAndPosition(keyDbt,null,SearchMode.SET,LockType.READ) & CursorImpl.FOUND) != 0;
        if (found) {
          NameLN nameLN=(NameLN)nameCursor.getCurrentLNAlreadyLatched(LockType.READ);
          assert nameLN != null;
          id=nameLN.getId();
          if (databaseHandle != null) {
            nameLocker.addToHandleMaps(new Long(nameLN.getNodeId()),databaseHandle);
          }
        }
      }
  finally {
        if (nameCursor != null) {
          this.hook303(nameCursor);
          nameCursor.close();
        }
      }
      if (id == null) {
        return null;
      }
 else {
        return getDb(id,-1,allowEviction,databaseName);
      }
    }
 catch (    UnsupportedEncodingException UEE) {
      throw new DatabaseException(UEE);
    }
  }
  /** 
 * Get a database object based on an id only. Used by recovery, cleaning and
 * other clients who have an id in hand, and don't have a resident node, to
 * find the matching database for a given log entry.
 */
  public DatabaseImpl getDb(  DatabaseId dbId) throws DatabaseException {
    return getDb(dbId,-1);
  }
  /** 
 * Get a database object based on an id only. Specify the lock timeout to
 * use, or -1 to use the default timeout. A timeout should normally only be
 * specified by daemons with their own timeout configuration. public for
 * unit tests.
 */
  public DatabaseImpl getDb(  DatabaseId dbId,  long lockTimeout) throws DatabaseException {
    return getDb(dbId,lockTimeout,true,null);
  }
  /** 
 * Get a database object based on an id only, caching the id-db mapping in
 * the given map.
 */
  public DatabaseImpl getDb(  DatabaseId dbId,  long lockTimeout,  Map dbCache) throws DatabaseException {
    if (dbCache.containsKey(dbId)) {
      return (DatabaseImpl)dbCache.get(dbId);
    }
 else {
      DatabaseImpl db=getDb(dbId,lockTimeout,true,null);
      dbCache.put(dbId,db);
      return db;
    }
  }
  /** 
 * Get a database object based on an id only. Specify the lock timeout to
 * use, or -1 to use the default timeout. A timeout should normally only be
 * specified by daemons with their own timeout configuration. public for
 * unit tests.
 * @param allowEvictionis whether eviction is allowed during cursor operations.
 */
  public DatabaseImpl getDb(  DatabaseId dbId,  long lockTimeout,  boolean allowEviction,  String dbNameIfAvailable) throws DatabaseException {
    if (dbId.equals(idDatabase.getId())) {
      return idDatabase;
    }
 else     if (dbId.equals(nameDatabase.getId())) {
      return nameDatabase;
    }
 else {
      Locker locker=new BasicLocker(envImpl);
      if (lockTimeout != -1) {
        locker.setLockTimeout(lockTimeout);
      }
      CursorImpl idCursor=null;
      DatabaseImpl foundDbImpl=null;
      while (true) {
        idCursor=new CursorImpl(idDatabase,locker);
        this.hook309(allowEviction,idCursor);
        try {
          DatabaseEntry keyDbt=new DatabaseEntry(dbId.getBytes());
          boolean found=(idCursor.searchAndPosition(keyDbt,new DatabaseEntry(),SearchMode.SET,LockType.READ) & CursorImpl.FOUND) != 0;
          if (found) {
            MapLN mapLN=(MapLN)idCursor.getCurrentLNAlreadyLatched(LockType.READ);
            assert mapLN != null;
            foundDbImpl=mapLN.getDatabase();
          }
          break;
        }
 catch (        DeadlockException DE) {
          idCursor.close();
          locker.operationEnd(false);
          locker=new BasicLocker(envImpl);
          if (lockTimeout != -1) {
            locker.setLockTimeout(lockTimeout);
          }
          idCursor=new CursorImpl(idDatabase,locker);
          this.hook310(allowEviction,idCursor);
          continue;
        }
 finally {
          this.hook304(idCursor);
          idCursor.close();
          locker.operationEnd(true);
        }
      }
      if (envImpl.isOpen()) {
        setDebugNameForDatabaseImpl(foundDbImpl,dbNameIfAvailable);
      }
      return foundDbImpl;
    }
  }
  private void setDebugNameForDatabaseImpl(  DatabaseImpl dbImpl,  String dbName) throws DatabaseException {
    if (dbImpl != null) {
      if (dbName != null) {
        dbImpl.setDebugDatabaseName(dbName);
      }
 else       if (dbImpl.getDebugName() == null) {
        dbImpl.setDebugDatabaseName(getDbName(dbImpl.getId()));
      }
    }
  }
  /** 
 * Rebuild the IN list after recovery.
 */
  public void rebuildINListMapDb() throws DatabaseException {
    idDatabase.getTree().rebuildINList();
  }
  /** 
 * Return the database name for a given db. Slow, must traverse. Used by
 * truncate and for debugging.
 */
  public String getDbName(  DatabaseId id) throws DatabaseException {
    if (id.equals(ID_DB_ID)) {
      return ID_DB_NAME;
    }
 else     if (id.equals(NAME_DB_ID)) {
      return NAME_DB_NAME;
    }
    Locker locker=null;
    CursorImpl cursor=null;
    try {
      locker=new BasicLocker(envImpl);
      cursor=new CursorImpl(nameDatabase,locker);
      DatabaseEntry keyDbt=new DatabaseEntry();
      DatabaseEntry dataDbt=new DatabaseEntry();
      String name=null;
      if (cursor.positionFirstOrLast(true,null)) {
        OperationStatus status=cursor.getCurrentAlreadyLatched(keyDbt,dataDbt,LockType.NONE,true);
        do {
          if (status == OperationStatus.SUCCESS) {
            NameLN nameLN=(NameLN)cursor.getCurrentLN(LockType.NONE);
            if (nameLN != null && nameLN.getId().equals(id)) {
              name=new String(keyDbt.getData(),"UTF-8");
              break;
            }
          }
          status=cursor.getNext(keyDbt,dataDbt,LockType.NONE,true,false);
        }
 while (status == OperationStatus.SUCCESS);
      }
      return name;
    }
 catch (    UnsupportedEncodingException UEE) {
      throw new DatabaseException(UEE);
    }
 finally {
      if (cursor != null) {
        this.hook305(cursor);
        cursor.close();
      }
      if (locker != null) {
        locker.operationEnd();
      }
    }
  }
  /** 
 * @return a list of database names held in the environment, as strings.
 */
  public List getDbNames() throws DatabaseException {
    List nameList=new ArrayList();
    Locker locker=null;
    CursorImpl cursor=null;
    try {
      locker=new BasicLocker(envImpl);
      cursor=new CursorImpl(nameDatabase,locker);
      DatabaseEntry keyDbt=new DatabaseEntry();
      DatabaseEntry dataDbt=new DatabaseEntry();
      if (cursor.positionFirstOrLast(true,null)) {
        OperationStatus status=cursor.getCurrentAlreadyLatched(keyDbt,dataDbt,LockType.READ,true);
        do {
          if (status == OperationStatus.SUCCESS) {
            String name=new String(keyDbt.getData(),"UTF-8");
            if (!isReservedDbName(name)) {
              nameList.add(name);
            }
          }
          status=cursor.getNext(keyDbt,dataDbt,LockType.READ,true,false);
        }
 while (status == OperationStatus.SUCCESS);
      }
      return nameList;
    }
 catch (    UnsupportedEncodingException UEE) {
      throw new DatabaseException(UEE);
    }
 finally {
      if (cursor != null) {
        cursor.close();
      }
      if (locker != null) {
        locker.operationEnd();
      }
    }
  }
  /** 
 * Returns true if the name is a reserved JE database name.
 */
  public boolean isReservedDbName(  String name){
    for (int i=0; i < RESERVED_DB_NAMES.length; i+=1) {
      if (RESERVED_DB_NAMES[i].equals(name)) {
        return true;
      }
    }
    return false;
  }
  /** 
 * @return the higest level node in the environment.
 */
  public int getHighestLevel() throws DatabaseException {
    RootLevel getLevel=new RootLevel(idDatabase);
    idDatabase.getTree().withRootLatchedShared(getLevel);
    int idHighLevel=getLevel.getRootLevel();
    getLevel=new RootLevel(nameDatabase);
    nameDatabase.getTree().withRootLatchedShared(getLevel);
    int nameHighLevel=getLevel.getRootLevel();
    return (nameHighLevel > idHighLevel) ? nameHighLevel : idHighLevel;
  }
private static class RootLevel implements WithRootLatched {
    private DatabaseImpl db;
    private int rootLevel;
    RootLevel(    DatabaseImpl db){
      this.db=db;
      rootLevel=0;
    }
    public IN doWork(    ChildReference root) throws DatabaseException {
      IN rootIN=(IN)root.fetchTarget(db,null);
      rootLevel=rootIN.getLevel();
      return null;
    }
    int getRootLevel(){
      return rootLevel;
    }
  }
  /** 
 * @see LoggableObject#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_ROOT;
  }
  /** 
 * @see LoggableObject#marshallOutsideWriteLatch Can be marshalled outside
 * the log write latch.
 */
  public boolean marshallOutsideWriteLatch(){
    return true;
  }
  /** 
 * @see LoggableObject#countAsObsoleteWhenLogged
 */
  public boolean countAsObsoleteWhenLogged(){
    return false;
  }
  /** 
 * @see LoggableObject#getLogSize
 */
  public int getLogSize(){
    return LogUtils.getIntLogSize() + idDatabase.getLogSize() + nameDatabase.getLogSize();
  }
  /** 
 * @see LoggableObject#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    LogUtils.writeInt(logBuffer,lastAllocatedDbId);
    idDatabase.writeToLog(logBuffer);
    nameDatabase.writeToLog(logBuffer);
  }
  /** 
 * @see LoggableObject#postLogWork
 */
  public void postLogWork(  long justLoggedLsn) throws DatabaseException {
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion) throws LogException {
    lastAllocatedDbId=LogUtils.readInt(itemBuffer);
    idDatabase.readFromLog(itemBuffer,entryTypeVersion);
    nameDatabase.readFromLog(itemBuffer,entryTypeVersion);
  }
  /** 
 * @see LogReadable#dumpLog
 */
  public void dumpLog(  StringBuffer sb,  boolean verbose){
    sb.append("<dbtree lastId = \"");
    sb.append(lastAllocatedDbId);
    sb.append("\">");
    sb.append("<idDb>");
    idDatabase.dumpLog(sb,verbose);
    sb.append("</idDb><nameDb>");
    nameDatabase.dumpLog(sb,verbose);
    sb.append("</nameDb>");
    sb.append("</dbtree>");
  }
  /** 
 * @see LogReadable#logEntryIsTransactional.
 */
  public boolean logEntryIsTransactional(){
    return false;
  }
  /** 
 * @see LogReadable#getTransactionId
 */
  public long getTransactionId(){
    return 0;
  }
  String dumpString(  int nSpaces){
    StringBuffer self=new StringBuffer();
    self.append(TreeUtils.indent(nSpaces));
    self.append("<dbTree lastDbId =\"");
    self.append(lastAllocatedDbId);
    self.append("\">");
    self.append('\n');
    self.append(idDatabase.dumpString(nSpaces + 1));
    self.append('\n');
    self.append(nameDatabase.dumpString(nSpaces + 1));
    self.append('\n');
    self.append("</dbtree>");
    return self.toString();
  }
  public String toString(){
    return dumpString(0);
  }
  /** 
 * For debugging.
 */
  public void dump() throws DatabaseException {
    idDatabase.getTree().dump();
    nameDatabase.getTree().dump();
  }
  protected void hook299(  CursorImpl cursor) throws DatabaseException {
  }
  protected void hook300(  NameLockResult result) throws DatabaseException, UnsupportedEncodingException {
  }
  protected void hook301(  NameLockResult result) throws DatabaseException {
  }
  protected void hook302(  NameLockResult result) throws DatabaseException {
  }
  protected void hook303(  CursorImpl nameCursor) throws DatabaseException, UnsupportedEncodingException {
  }
  protected void hook304(  CursorImpl idCursor) throws DatabaseException {
  }
  protected void hook305(  CursorImpl cursor) throws DatabaseException {
  }
  protected void hook306(  boolean allowEviction,  CursorImpl idCursor) throws DatabaseException, UnsupportedEncodingException {
  }
  protected void hook307(  boolean allowEviction,  CursorImpl nameCursor) throws DatabaseException, UnsupportedEncodingException {
  }
  protected void hook308(  boolean allowEviction,  CursorImpl nameCursor) throws DatabaseException, UnsupportedEncodingException {
  }
  protected void hook309(  boolean allowEviction,  CursorImpl idCursor) throws DatabaseException {
  }
  protected void hook310(  boolean allowEviction,  CursorImpl idCursor) throws DatabaseException {
  }
}
