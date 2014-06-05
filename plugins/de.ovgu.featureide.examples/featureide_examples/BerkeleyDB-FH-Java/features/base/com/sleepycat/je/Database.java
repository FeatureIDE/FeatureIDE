package com.sleepycat.je;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.dbi.GetMode;
import com.sleepycat.je.dbi.PutMode;
import com.sleepycat.je.dbi.CursorImpl.SearchMode;
import com.sleepycat.je.txn.Locker;
import com.sleepycat.je.txn.LockerFactory;
import com.sleepycat.je.utilint.TinyHashSet;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
public class Database {
static class DbState {
    private String stateName;
    DbState(    String stateName){
      this.stateName=stateName;
    }
    public String toString(){
      return "DbState." + stateName;
    }
  }
  static DbState OPEN=new DbState("OPEN");
  static DbState CLOSED=new DbState("CLOSED");
  static DbState INVALID=new DbState("INVALID");
  private DbState state;
  Environment envHandle;
  private DatabaseImpl databaseImpl;
  DatabaseConfig configuration;
  private boolean isWritable;
  Locker handleLocker;
  private TinyHashSet cursors=new TinyHashSet();
  private List triggerList;
  /** 
 * Creates a database but does not open or fully initialize it.
 * Is protected for use in compat package.
 */
  protected Database(  Environment env){
    this.envHandle=env;
    handleLocker=null;
  }
  /** 
 * Create a database, called by Environment.
 */
  void initNew(  Environment env,  Locker locker,  String databaseName,  DatabaseConfig dbConfig) throws DatabaseException {
    if (dbConfig.getReadOnly()) {
      throw new DatabaseException("DatabaseConfig.setReadOnly() must be set to false " + "when creating a Database");
    }
    init(env,dbConfig);
    EnvironmentImpl environmentImpl=DbInternal.envGetEnvironmentImpl(envHandle);
    databaseImpl=environmentImpl.createDb(locker,databaseName,dbConfig,this);
    databaseImpl.addReferringHandle(this);
  }
  /** 
 * Open a database, called by Environment.
 */
  void initExisting(  Environment env,  Locker locker,  DatabaseImpl databaseImpl,  DatabaseConfig dbConfig) throws DatabaseException {
    validateConfigAgainstExistingDb(dbConfig,databaseImpl);
    init(env,dbConfig);
    this.databaseImpl=databaseImpl;
    databaseImpl.addReferringHandle(this);
    configuration.setSortedDuplicates(databaseImpl.getSortedDuplicates());
    configuration.setTransactional(databaseImpl.isTransactional());
  }
  private void init(  Environment env,  DatabaseConfig config) throws DatabaseException {
    handleLocker=null;
    envHandle=env;
    configuration=config.cloneConfig();
    isWritable=!configuration.getReadOnly();
    state=OPEN;
  }
  /** 
 * See if this new handle's configuration is compatible with the
 * pre-existing database.
 */
  private void validateConfigAgainstExistingDb(  DatabaseConfig config,  DatabaseImpl databaseImpl) throws DatabaseException {
    if (!config.getUseExistingConfig()) {
      if (databaseImpl.getSortedDuplicates() != config.getSortedDuplicates()) {
        throw new DatabaseException("You can't open a Database with a duplicatesAllowed " + "configuration of " + config.getSortedDuplicates() + " if the underlying database was created with a "+ "duplicatesAllowedSetting of "+ databaseImpl.getSortedDuplicates()+ ".");
      }
    }
    if (databaseImpl.hasOpenHandles()) {
      if (!config.getUseExistingConfig()) {
        if (config.getTransactional() != databaseImpl.isTransactional()) {
          throw new DatabaseException("You can't open a Database with a transactional " + "configuration of " + config.getTransactional() + " if the underlying database was created with a "+ "transactional configuration of "+ databaseImpl.isTransactional()+ ".");
        }
      }
    }
 else {
      databaseImpl.setTransactional(config.getTransactional());
    }
    if (config.getOverrideBtreeComparator()) {
      databaseImpl.setBtreeComparator(config.getBtreeComparator());
    }
    if (config.getOverrideDuplicateComparator()) {
      databaseImpl.setDuplicateComparator(config.getDuplicateComparator());
    }
  }
  public synchronized void close() throws DatabaseException {
    StringBuffer errors=null;
    checkEnv();
    checkProhibitedDbState(CLOSED,"Can't close Database:");
    this.hook44();
    removeAllTriggers();
    envHandle.removeReferringHandle(this);
    if (cursors.size() > 0) {
      errors=new StringBuffer("There are open cursors against the database.\n");
      errors.append("They will be closed.\n");
      Iterator iter=cursors.copy().iterator();
      while (iter.hasNext()) {
        Cursor dbc=(Cursor)iter.next();
        try {
          dbc.close();
        }
 catch (        DatabaseException DBE) {
          errors.append("Exception while closing cursors:\n");
          errors.append(DBE.toString());
        }
      }
    }
    if (databaseImpl != null) {
      databaseImpl.removeReferringHandle(this);
      databaseImpl=null;
      handleLocker.setHandleLockOwner(true,this,true);
      handleLocker.operationEnd(true);
      state=CLOSED;
    }
    if (errors != null) {
      throw new DatabaseException(errors.toString());
    }
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public Sequence openSequence(  Transaction txn,  DatabaseEntry key,  SequenceConfig config) throws DatabaseException {
    checkEnv();
    DatabaseUtil.checkForNullDbt(key,"key",true);
    checkRequiredDbState(OPEN,"Can't call Database.openSequence:");
    checkWritable("openSequence");
    this.hook45(txn,key);
    return new Sequence(this,txn,key,config);
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void removeSequence(  Transaction txn,  DatabaseEntry key) throws DatabaseException {
    delete(txn,key);
  }
  public synchronized Cursor openCursor(  Transaction txn,  CursorConfig cursorConfig) throws DatabaseException {
    checkEnv();
    checkRequiredDbState(OPEN,"Can't open a cursor");
    CursorConfig useConfig=(cursorConfig == null) ? CursorConfig.DEFAULT : cursorConfig;
    if (useConfig.getReadUncommitted() && useConfig.getReadCommitted()) {
      throw new IllegalArgumentException("Only one may be specified: ReadCommitted or ReadUncommitted");
    }
    this.hook46(txn,cursorConfig);
    Cursor ret=newDbcInstance(txn,useConfig);
    return ret;
  }
  /** 
 * Is overridden by SecondaryDatabase.
 */
  Cursor newDbcInstance(  Transaction txn,  CursorConfig cursorConfig) throws DatabaseException {
    return new Cursor(this,txn,cursorConfig);
  }
  public OperationStatus delete(  Transaction txn,  DatabaseEntry key) throws DatabaseException {
    checkEnv();
    DatabaseUtil.checkForNullDbt(key,"key",true);
    checkRequiredDbState(OPEN,"Can't call Database.delete:");
    checkWritable("delete");
    this.hook47(txn,key);
    OperationStatus commitStatus=OperationStatus.NOTFOUND;
    Locker locker=null;
    try {
      locker=LockerFactory.getWritableLocker(envHandle,txn,isTransactional());
      commitStatus=deleteInternal(locker,key);
      return commitStatus;
    }
  finally {
      if (locker != null) {
        locker.operationEnd(commitStatus);
      }
    }
  }
  /** 
 * Internal version of delete() that does no parameter checking.  Notify
 * triggers.  Deletes all duplicates.
 */
  OperationStatus deleteInternal(  Locker locker,  DatabaseEntry key) throws DatabaseException {
    Cursor cursor=null;
    try {
      cursor=new Cursor(this,locker,null);
      cursor.setNonCloning(true);
      OperationStatus commitStatus=OperationStatus.NOTFOUND;
      DatabaseEntry oldData=new DatabaseEntry();
      OperationStatus searchStatus=cursor.search(key,oldData,LockMode.RMW,SearchMode.SET);
      if (searchStatus == OperationStatus.SUCCESS) {
        do {
          if (hasTriggers()) {
            notifyTriggers(locker,key,oldData,null);
          }
          commitStatus=cursor.deleteNoNotify();
          if (commitStatus != OperationStatus.SUCCESS) {
            return commitStatus;
          }
          if (databaseImpl.getSortedDuplicates()) {
            searchStatus=cursor.retrieveNext(key,oldData,LockMode.RMW,GetMode.NEXT_DUP);
          }
 else {
            searchStatus=OperationStatus.NOTFOUND;
          }
        }
 while (searchStatus == OperationStatus.SUCCESS);
        commitStatus=OperationStatus.SUCCESS;
      }
      return commitStatus;
    }
  finally {
      if (cursor != null) {
        cursor.close();
      }
    }
  }
  public OperationStatus get(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    checkEnv();
    DatabaseUtil.checkForNullDbt(key,"key",true);
    DatabaseUtil.checkForNullDbt(data,"data",false);
    checkRequiredDbState(OPEN,"Can't call Database.get:");
    this.hook48(txn,key,lockMode);
    CursorConfig cursorConfig=CursorConfig.DEFAULT;
    if (lockMode == LockMode.READ_COMMITTED) {
      cursorConfig=CursorConfig.READ_COMMITTED;
      lockMode=null;
    }
    Cursor cursor=null;
    try {
      cursor=new Cursor(this,txn,cursorConfig);
      cursor.setNonCloning(true);
      return cursor.search(key,data,lockMode,SearchMode.SET);
    }
  finally {
      if (cursor != null) {
        cursor.close();
      }
    }
  }
  public OperationStatus getSearchBoth(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
    checkEnv();
    DatabaseUtil.checkForNullDbt(key,"key",true);
    DatabaseUtil.checkForNullDbt(data,"data",true);
    checkRequiredDbState(OPEN,"Can't call Database.getSearchBoth:");
    this.hook49(txn,key,data,lockMode);
    CursorConfig cursorConfig=CursorConfig.DEFAULT;
    if (lockMode == LockMode.READ_COMMITTED) {
      cursorConfig=CursorConfig.READ_COMMITTED;
      lockMode=null;
    }
    Cursor cursor=null;
    try {
      cursor=new Cursor(this,txn,cursorConfig);
      cursor.setNonCloning(true);
      return cursor.search(key,data,lockMode,SearchMode.BOTH);
    }
  finally {
      if (cursor != null) {
        cursor.close();
      }
    }
  }
  public OperationStatus put(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    checkEnv();
    DatabaseUtil.checkForNullDbt(key,"key",true);
    DatabaseUtil.checkForNullDbt(data,"data",true);
    DatabaseUtil.checkForPartialKey(key);
    checkRequiredDbState(OPEN,"Can't call Database.put");
    checkWritable("put");
    this.hook50(txn,key,data);
    return putInternal(txn,key,data,PutMode.OVERWRITE);
  }
  public OperationStatus putNoOverwrite(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    checkEnv();
    DatabaseUtil.checkForNullDbt(key,"key",true);
    DatabaseUtil.checkForNullDbt(data,"data",true);
    DatabaseUtil.checkForPartialKey(key);
    checkRequiredDbState(OPEN,"Can't call Database.putNoOverWrite");
    checkWritable("putNoOverwrite");
    this.hook51(txn,key,data);
    return putInternal(txn,key,data,PutMode.NOOVERWRITE);
  }
  public OperationStatus putNoDupData(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
    checkEnv();
    DatabaseUtil.checkForNullDbt(key,"key",true);
    DatabaseUtil.checkForNullDbt(data,"data",true);
    DatabaseUtil.checkForPartialKey(key);
    checkRequiredDbState(OPEN,"Can't call Database.putNoDupData");
    checkWritable("putNoDupData");
    this.hook52(txn,key,data);
    return putInternal(txn,key,data,PutMode.NODUP);
  }
  /** 
 * Internal version of put() that does no parameter checking.
 */
  OperationStatus putInternal(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data,  PutMode putMode) throws DatabaseException {
    Locker locker=null;
    Cursor cursor=null;
    OperationStatus commitStatus=OperationStatus.KEYEXIST;
    try {
      locker=LockerFactory.getWritableLocker(envHandle,txn,isTransactional());
      cursor=new Cursor(this,locker,null);
      cursor.setNonCloning(true);
      commitStatus=cursor.putInternal(key,data,putMode);
      return commitStatus;
    }
  finally {
      if (cursor != null) {
        cursor.close();
      }
      if (locker != null) {
        locker.operationEnd(commitStatus);
      }
    }
  }
  /** 
 */
  public JoinCursor join(  Cursor[] cursors,  JoinConfig config) throws DatabaseException {
    checkEnv();
    checkRequiredDbState(OPEN,"Can't call Database.join");
    DatabaseUtil.checkForNullParam(cursors,"cursors");
    if (cursors.length == 0) {
      throw new IllegalArgumentException("At least one cursor is required.");
    }
    Locker locker=cursors[0].getCursorImpl().getLocker();
    if (!locker.isTransactional()) {
      EnvironmentImpl env=envHandle.getEnvironmentImpl();
      for (int i=1; i < cursors.length; i+=1) {
        Locker locker2=cursors[i].getCursorImpl().getLocker();
        if (locker2.isTransactional()) {
          throw new IllegalArgumentException("All cursors must use the same transaction.");
        }
        EnvironmentImpl env2=cursors[i].getDatabaseImpl().getDbEnvironment();
        if (env != env2) {
          throw new IllegalArgumentException("All cursors must use the same environment.");
        }
      }
      locker=null;
    }
 else {
      for (int i=1; i < cursors.length; i+=1) {
        Locker locker2=cursors[i].getCursorImpl().getLocker();
        if (locker.getTxnLocker() != locker2.getTxnLocker()) {
          throw new IllegalArgumentException("All cursors must use the same transaction.");
        }
      }
    }
    return new JoinCursor(locker,this,cursors,config);
  }
  public void preload(  long maxBytes) throws DatabaseException {
    checkEnv();
    checkRequiredDbState(OPEN,"Can't call Database.preload");
    this.hook55();
    PreloadConfig config=new PreloadConfig();
    config.setMaxBytes(maxBytes);
    databaseImpl.preload(config);
  }
  public void preload(  long maxBytes,  long maxMillisecs) throws DatabaseException {
    checkEnv();
    checkRequiredDbState(OPEN,"Can't call Database.preload");
    this.hook56();
    PreloadConfig config=new PreloadConfig();
    config.setMaxBytes(maxBytes);
    config.setMaxMillisecs(maxMillisecs);
    databaseImpl.preload(config);
  }
  public PreloadStats preload(  PreloadConfig config) throws DatabaseException {
    checkEnv();
    checkRequiredDbState(OPEN,"Can't call Database.preload");
    this.hook57();
    return databaseImpl.preload(config);
  }
  public String getDatabaseName() throws DatabaseException {
    checkEnv();
    if (databaseImpl != null) {
      return databaseImpl.getName();
    }
 else {
      return null;
    }
  }
  String getDebugName(){
    if (databaseImpl != null) {
      return databaseImpl.getDebugName();
    }
 else {
      return null;
    }
  }
  public DatabaseConfig getConfig() throws DatabaseException {
    DatabaseConfig showConfig=configuration.cloneConfig();
    Comparator btComp=(databaseImpl == null ? null : databaseImpl.getBtreeComparator());
    Comparator dupComp=(databaseImpl == null ? null : databaseImpl.getDuplicateComparator());
    showConfig.setBtreeComparator(btComp == null ? null : btComp.getClass());
    showConfig.setDuplicateComparator(dupComp == null ? null : dupComp.getClass());
    return showConfig;
  }
  /** 
 * Equivalent to getConfig().getTransactional() but cheaper.
 */
  boolean isTransactional() throws DatabaseException {
    return databaseImpl.isTransactional();
  }
  public Environment getEnvironment() throws DatabaseException {
    return envHandle;
  }
  public List getSecondaryDatabases() throws DatabaseException {
    List list=new ArrayList();
    if (hasTriggers()) {
      acquireTriggerListReadLock();
      this.hook53(list);
    }
 else {
    }
    return list;
  }
  /** 
 * @return true if the Database was opened read/write.
 */
  boolean isWritable(){
    return isWritable;
  }
  /** 
 * Return the databaseImpl object instance.
 */
  DatabaseImpl getDatabaseImpl(){
    return databaseImpl;
  }
  /** 
 * The handleLocker is the one that holds the db handle lock.
 */
  void setHandleLocker(  Locker locker){
    handleLocker=locker;
  }
  synchronized void removeCursor(  Cursor dbc){
    cursors.remove(dbc);
  }
  synchronized void addCursor(  Cursor dbc){
    cursors.add(dbc);
  }
  /** 
 * @throws DatabaseException if the Database state is not this value.
 */
  void checkRequiredDbState(  DbState required,  String msg) throws DatabaseException {
    if (state != required) {
      throw new DatabaseException(msg + " Database state can't be " + state+ " must be "+ required);
    }
  }
  /** 
 * @throws DatabaseException if the Database state is this value.
 */
  void checkProhibitedDbState(  DbState prohibited,  String msg) throws DatabaseException {
    if (state == prohibited) {
      throw new DatabaseException(msg + " Database state must not be " + prohibited);
    }
  }
  /** 
 * @throws RunRecoveryException if the underlying environment is
 * invalid
 */
  void checkEnv() throws RunRecoveryException {
    EnvironmentImpl env=envHandle.getEnvironmentImpl();
    if (env != null) {
      env.checkIfInvalid();
    }
  }
  /** 
 * Invalidate the handle, called by txn.abort by way of DbInternal.
 */
  synchronized void invalidate(){
    state=INVALID;
    envHandle.removeReferringHandle(this);
    if (databaseImpl != null) {
      databaseImpl.removeReferringHandle(this);
    }
  }
  /** 
 * Check that write operations aren't used on a readonly Database.
 */
  private void checkWritable(  String operation) throws DatabaseException {
    if (!isWritable) {
      throw new DatabaseException("Database is Read Only: " + operation);
    }
  }
  /** 
 * Returns whether any triggers are currently associated with this primary.
 * Note that an update of the trigger list may be in progress and this
 * method does not wait for that update to be completed.
 */
  boolean hasTriggers(){
    return triggerList != null;
  }
  /** 
 * Gets a read-lock on the list of triggers.  releaseTriggerListReadLock()
 * must be called to release the lock.  Called by all primary put and
 * delete operations.
 */
  private void acquireTriggerListReadLock() throws DatabaseException {
    new Database_acquireTriggerListReadLock(this).execute();
  }
  /** 
 * Gets a write lock on the list of triggers.  An empty list is created if
 * necessary, so null is never returned.  releaseTriggerListWriteLock()
 * must always be called to release the lock.
 */
  private void acquireTriggerListWriteLock() throws DatabaseException {
    new Database_acquireTriggerListWriteLock(this).execute();
  }
  /** 
 * Releases a lock acquired by calling acquireTriggerListWriteLock().  If
 * the list is now empty then it is set to null, that is, hasTriggers()
 * will subsequently return false.
 */
  private void releaseTriggerListWriteLock() throws DatabaseException {
    new Database_releaseTriggerListWriteLock(this).execute();
  }
  /** 
 * Adds a given trigger to the list of triggers.  Called while opening
 * a SecondaryDatabase.
 * @param insertAtFront true to insert at the front, or false to append.
 */
  void addTrigger(  DatabaseTrigger trigger,  boolean insertAtFront) throws DatabaseException {
    acquireTriggerListWriteLock();
    try {
      if (insertAtFront) {
        triggerList.add(0,trigger);
      }
 else {
        triggerList.add(trigger);
      }
      trigger.triggerAdded(this);
    }
  finally {
      releaseTriggerListWriteLock();
    }
  }
  /** 
 * Removes a given trigger from the list of triggers.  Called by
 * SecondaryDatabase.close().
 */
  void removeTrigger(  DatabaseTrigger trigger) throws DatabaseException {
    acquireTriggerListWriteLock();
    try {
      triggerList.remove(trigger);
      trigger.triggerRemoved(this);
    }
  finally {
      releaseTriggerListWriteLock();
    }
  }
  /** 
 * Clears the list of triggers.  Called by close(), this allows closing the
 * primary before its secondaries, although we document that secondaries
 * should be closed first.
 */
  private void removeAllTriggers() throws DatabaseException {
    acquireTriggerListWriteLock();
    try {
      for (int i=0; i < triggerList.size(); i+=1) {
        DatabaseTrigger trigger=(DatabaseTrigger)triggerList.get(i);
        trigger.triggerRemoved(this);
      }
      triggerList.clear();
    }
  finally {
      releaseTriggerListWriteLock();
    }
  }
  /** 
 * Notifies associated triggers when a put() or delete() is performed on
 * the primary.  This method is normally called only if hasTriggers() has
 * returned true earlier.  This avoids acquiring a shared latch for
 * primaries with no triggers.  If a trigger is added during the update
 * process, there is no requirement to immediately start updating it.
 * @param locker the internal locker.
 * @param priKey the primary key.
 * @param oldData the primary data before the change, or null if the record
 * did not previously exist.
 * @param newData the primary data after the change, or null if the record
 * has been deleted.
 */
  void notifyTriggers(  Locker locker,  DatabaseEntry priKey,  DatabaseEntry oldData,  DatabaseEntry newData) throws DatabaseException {
    acquireTriggerListReadLock();
    this.hook54(locker,priKey,oldData,newData);
  }
@MethodObject static class Database_acquireTriggerListReadLock {
    Database_acquireTriggerListReadLock(    Database _this){
      this._this=_this;
    }
    void execute() throws DatabaseException {
      if (_this.triggerList == null) {
        _this.triggerList=new ArrayList();
      }
    }
    protected Database _this;
    protected EnvironmentImpl env;
  }
@MethodObject static class Database_acquireTriggerListWriteLock {
    Database_acquireTriggerListWriteLock(    Database _this){
      this._this=_this;
    }
    void execute() throws DatabaseException {
      if (_this.triggerList == null) {
        _this.triggerList=new ArrayList();
      }
    }
    protected Database _this;
    protected EnvironmentImpl env;
  }
@MethodObject static class Database_releaseTriggerListWriteLock {
    Database_releaseTriggerListWriteLock(    Database _this){
      this._this=_this;
    }
    void execute() throws DatabaseException {
      if (_this.triggerList.size() == 0) {
        _this.triggerList=null;
      }
    }
    protected Database _this;
    protected EnvironmentImpl env;
  }
  protected void hook44() throws DatabaseException {
  }
  protected void hook45(  Transaction txn,  DatabaseEntry key) throws DatabaseException {
  }
  protected void hook46(  Transaction txn,  CursorConfig cursorConfig) throws DatabaseException {
  }
  protected void hook47(  Transaction txn,  DatabaseEntry key) throws DatabaseException {
  }
  protected void hook48(  Transaction txn,  DatabaseEntry key,  LockMode lockMode) throws DatabaseException {
  }
  protected void hook49(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data,  LockMode lockMode) throws DatabaseException {
  }
  protected void hook50(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
  }
  protected void hook51(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
  }
  protected void hook52(  Transaction txn,  DatabaseEntry key,  DatabaseEntry data) throws DatabaseException {
  }
  protected void hook53(  List list) throws DatabaseException {
    for (int i=0; i < triggerList.size(); i+=1) {
      Object obj=triggerList.get(i);
      if (obj instanceof SecondaryTrigger) {
        list.add(((SecondaryTrigger)obj).getDb());
      }
    }
  }
  protected void hook54(  Locker locker,  DatabaseEntry priKey,  DatabaseEntry oldData,  DatabaseEntry newData) throws DatabaseException {
    for (int i=0; i < triggerList.size(); i+=1) {
      DatabaseTrigger trigger=(DatabaseTrigger)triggerList.get(i);
      trigger.databaseUpdated(this,locker,priKey,oldData,newData);
    }
  }
  protected void hook55() throws DatabaseException {
  }
  protected void hook56() throws DatabaseException {
  }
  protected void hook57() throws DatabaseException {
  }
}
