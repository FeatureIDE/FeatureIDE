package com.sleepycat.je.dbi;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;
import com.sleepycat.je.CheckpointConfig;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.EnvironmentConfig;
import com.sleepycat.je.EnvironmentMutableConfig;
import com.sleepycat.je.LockStats;
import com.sleepycat.je.RunRecoveryException;
import com.sleepycat.je.Transaction;
import com.sleepycat.je.TransactionConfig;
import com.sleepycat.je.cleaner.Cleaner;
import com.sleepycat.je.cleaner.UtilizationProfile;
import com.sleepycat.je.cleaner.UtilizationTracker;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.log.FileManager;
import com.sleepycat.je.log.LogManager;
import com.sleepycat.je.log.SyncedLogManager;
import com.sleepycat.je.recovery.Checkpointer;
import com.sleepycat.je.recovery.RecoveryInfo;
import com.sleepycat.je.recovery.RecoveryManager;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.BINReference;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.Key;
import com.sleepycat.je.txn.Locker;
import com.sleepycat.je.txn.Txn;
import com.sleepycat.je.txn.TxnManager;
import com.sleepycat.je.utilint.DbLsn;
import com.sleepycat.je.utilint.PropUtil;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
/** 
 * Underlying Environment implementation. There is a single instance for any
 * database environment opened by the application.
 */
public class EnvironmentImpl implements EnvConfigObserver {
  private static final boolean TEST_NO_LOCKING_MODE=false;
  private DbEnvState envState;
  private boolean closing;
  private File envHome;
  private int referenceCount;
  private boolean isTransactional;
  private boolean isNoLocking;
  private boolean isReadOnly;
  private MemoryBudget memoryBudget;
  private long lockTimeout;
  private long txnTimeout;
  private DbTree dbMapTree;
  private long mapTreeRootLsn=DbLsn.NULL_LSN;
  private INList inMemoryINs;
  private DbConfigManager configManager;
  private List configObservers;
  protected LogManager logManager;
  private FileManager fileManager;
  private TxnManager txnManager;
  private Checkpointer checkpointer;
  private Cleaner cleaner;
  private RecoveryInfo lastRecoveryInfo;
  private RunRecoveryException savedInvalidatingException;
  private static boolean forcedYield=false;
  private static int threadLocalReferenceCount=0;
  /** 
 * DbPrintLog doesn't need btree and dup comparators to function properly
 * don't require any instantiations. This flag, if true, indicates that
 * we've been called from DbPrintLog.
 */
  private static boolean noComparators=false;
  public static final boolean JAVA5_AVAILABLE;
  private static final String DISABLE_JAVA_ADLER32="je.disable.java.adler32";
static {
    boolean ret=false;
    if (System.getProperty(DISABLE_JAVA_ADLER32) == null) {
      String javaVersion=System.getProperty("java.version");
      if (javaVersion != null && !javaVersion.startsWith("1.4.")) {
        ret=true;
      }
    }
    JAVA5_AVAILABLE=ret;
  }
  /** 
 * Create a database environment to represent the data in envHome. dbHome.
 * Properties from the je.properties file in that directory are used to
 * initialize the system wide property bag. Properties passed to this method
 * are used to influence the open itself.
 * @param envHomeabsolute path of the database environment home directory
 * @param envConfig
 * @throws DatabaseExceptionon all other failures
 */
  public EnvironmentImpl(  File envHome,  EnvironmentConfig envConfig) throws DatabaseException {
    try {
      this.envHome=envHome;
      envState=DbEnvState.INIT;
      this.hook323();
      configManager=new DbConfigManager(envConfig);
      configObservers=new ArrayList();
      addConfigObserver(this);
      memoryBudget=new MemoryBudget(this,configManager);
      this.hook336(envHome);
      forcedYield=configManager.getBoolean(EnvironmentParams.ENV_FORCED_YIELD);
      isTransactional=configManager.getBoolean(EnvironmentParams.ENV_INIT_TXN);
      isNoLocking=!(configManager.getBoolean(EnvironmentParams.ENV_INIT_LOCKING));
      if (isTransactional && isNoLocking) {
        if (TEST_NO_LOCKING_MODE) {
          isNoLocking=!isTransactional;
        }
 else {
          throw new IllegalArgumentException("Can't set 'je.env.isNoLocking' and " + "'je.env.isTransactional';");
        }
      }
      this.hook322();
      isReadOnly=configManager.getBoolean(EnvironmentParams.ENV_RDONLY);
      fileManager=new FileManager(this,envHome,isReadOnly);
      if (!envConfig.getAllowCreate() && !fileManager.filesExist()) {
        throw new DatabaseException("Enviroment creation isn't allowed, " + " but there is no pre-existing " + " environment in "+ envHome);
      }
      this.hook321();
      inMemoryINs=new INList(this);
      txnManager=new TxnManager(this);
      createDaemons();
      dbMapTree=new DbTree(this);
      referenceCount=0;
      this.hook320();
      if (configManager.getBoolean(EnvironmentParams.ENV_RECOVERY)) {
        try {
          RecoveryManager recoveryManager=new RecoveryManager(this);
          lastRecoveryInfo=recoveryManager.recover(isReadOnly);
        }
  finally {
          try {
            logManager.flush();
            fileManager.clear();
          }
 catch (          IOException e) {
            throw new DatabaseException(e.getMessage());
          }
        }
      }
 else {
        isReadOnly=true;
        noComparators=true;
      }
      runOrPauseDaemons(configManager);
      lockTimeout=PropUtil.microsToMillis(configManager.getLong(EnvironmentParams.LOCK_TIMEOUT));
      txnTimeout=PropUtil.microsToMillis(configManager.getLong(EnvironmentParams.TXN_TIMEOUT));
      this.hook335();
      open();
    }
 catch (    DatabaseException e) {
      if (fileManager != null) {
        try {
          fileManager.close();
        }
 catch (        IOException IOE) {
        }
      }
      throw e;
    }
  }
  /** 
 * Respond to config updates.
 */
  public void envConfigUpdate(  DbConfigManager mgr) throws DatabaseException {
    runOrPauseDaemons(mgr);
  }
  /** 
 * Read configurations for daemons, instantiate.
 */
  private void createDaemons() throws DatabaseException {
    new EnvironmentImpl_createDaemons(this).execute();
  }
  /** 
 * Run or pause daemons, depending on config properties.
 */
  private void runOrPauseDaemons(  DbConfigManager mgr) throws DatabaseException {
    if (!isReadOnly) {
      this.hook330(mgr);
      this.hook333(mgr);
      this.hook326(mgr);
    }
    this.hook317(mgr);
  }
  /** 
 * Returns the UtilizationTracker.
 */
  public UtilizationTracker getUtilizationTracker(){
    return cleaner.getUtilizationTracker();
  }
  /** 
 * Returns the UtilizationProfile.
 */
  public UtilizationProfile getUtilizationProfile(){
    return cleaner.getUtilizationProfile();
  }
  /** 
 * Log the map tree root and save the LSN.
 */
  public void logMapTreeRoot() throws DatabaseException {
    mapTreeRootLsn=logManager.log(dbMapTree);
  }
  /** 
 * Force a rewrite of the map tree root if required.
 */
  public void rewriteMapTreeRoot(  long cleanerTargetLsn) throws DatabaseException {
    if (DbLsn.compareTo(cleanerTargetLsn,mapTreeRootLsn) == 0) {
      mapTreeRootLsn=logManager.log(dbMapTree);
    }
  }
  /** 
 * @return the mapping tree root LSN.
 */
  public long getRootLsn(){
    return mapTreeRootLsn;
  }
  /** 
 * Set the mapping tree from the log. Called during recovery.
 */
  public void readMapTreeFromLog(  long rootLsn) throws DatabaseException {
    dbMapTree=(DbTree)logManager.get(rootLsn);
    dbMapTree.setEnvironmentImpl(this);
    this.hook324(rootLsn);
  }
  /** 
 * Not much to do, mark state.
 */
  public void open(){
    envState=DbEnvState.OPEN;
  }
  /** 
 * Invalidate the environment. Done when a fatal exception
 * (RunRecoveryException) is thrown.
 */
  public void invalidate(  RunRecoveryException e){
    savedInvalidatingException=e;
    envState=DbEnvState.INVALID;
    requestShutdownDaemons();
  }
  /** 
 * @return true if environment is open.
 */
  public boolean isOpen(){
    return (envState == DbEnvState.OPEN);
  }
  /** 
 * @return true if close has begun, although the state may still be open.
 */
  public boolean isClosing(){
    return closing;
  }
  public boolean isClosed(){
    return (envState == DbEnvState.CLOSED);
  }
  /** 
 * When a RunRecoveryException occurs or the environment is closed, further
 * writing can cause log corruption.
 */
  public boolean mayNotWrite(){
    return (envState == DbEnvState.INVALID) || (envState == DbEnvState.CLOSED);
  }
  public void checkIfInvalid() throws RunRecoveryException {
    if (envState == DbEnvState.INVALID) {
      savedInvalidatingException.setAlreadyThrown();
      throw savedInvalidatingException;
    }
  }
  public void checkNotClosed() throws DatabaseException {
    if (envState == DbEnvState.CLOSED) {
      throw new DatabaseException("Attempt to use a Environment that has been closed.");
    }
  }
  public synchronized void close() throws DatabaseException {
    if (--referenceCount <= 0) {
      doClose(true);
    }
  }
  public synchronized void close(  boolean doCheckpoint) throws DatabaseException {
    if (--referenceCount <= 0) {
      doClose(doCheckpoint);
    }
  }
  private void doClose(  boolean doCheckpoint) throws DatabaseException {
    StringBuffer errors=new StringBuffer();
    try {
      this.hook319();
      try {
        envState.checkState(DbEnvState.VALID_FOR_CLOSE,DbEnvState.CLOSED);
      }
 catch (      DatabaseException DBE) {
        throw DBE;
      }
      requestShutdownDaemons();
      if (doCheckpoint && !isReadOnly && (envState != DbEnvState.INVALID)&& logManager.getLastLsnAtRecovery() != fileManager.getLastUsedLsn()) {
        CheckpointConfig ckptConfig=new CheckpointConfig();
        ckptConfig.setForce(true);
        ckptConfig.setMinimizeRecoveryTime(true);
        try {
          invokeCheckpoint(ckptConfig,false,"close");
        }
 catch (        DatabaseException IE) {
          errors.append("\nException performing checkpoint: ");
          errors.append(IE.toString()).append("\n");
        }
      }
      try {
        shutdownDaemons();
      }
 catch (      InterruptedException IE) {
        errors.append("\nException shutting down daemon threads: ");
        errors.append(IE.toString()).append("\n");
      }
      this.hook318();
      try {
        logManager.flush();
      }
 catch (      DatabaseException DBE) {
        errors.append("\nException flushing log manager: ");
        errors.append(DBE.toString()).append("\n");
      }
      try {
        fileManager.clear();
      }
 catch (      IOException IOE) {
        errors.append("\nException clearing file manager: ");
        errors.append(IOE.toString()).append("\n");
      }
catch (      DatabaseException DBE) {
        errors.append("\nException clearing file manager: ");
        errors.append(DBE.toString()).append("\n");
      }
      try {
        fileManager.close();
      }
 catch (      IOException IOE) {
        errors.append("\nException clearing file manager: ");
        errors.append(IOE.toString()).append("\n");
      }
catch (      DatabaseException DBE) {
        errors.append("\nException clearing file manager: ");
        errors.append(DBE.toString()).append("\n");
      }
      try {
        inMemoryINs.clear();
      }
 catch (      DatabaseException DBE) {
        errors.append("\nException closing file manager: ");
        errors.append(DBE.toString()).append("\n");
      }
      this.hook337();
      DbEnvPool.getInstance().remove(envHome);
      this.hook325(errors);
    }
  finally {
      envState=DbEnvState.CLOSED;
    }
    if (errors.length() > 0 && savedInvalidatingException == null) {
      throw new RunRecoveryException(this,errors.toString());
    }
  }
  public synchronized void closeAfterRunRecovery() throws DatabaseException {
    try {
      shutdownDaemons();
    }
 catch (    InterruptedException IE) {
    }
    try {
      fileManager.clear();
    }
 catch (    Exception e) {
    }
    try {
      fileManager.close();
    }
 catch (    Exception e) {
    }
    DbEnvPool.getInstance().remove(envHome);
  }
  public synchronized void forceClose() throws DatabaseException {
    referenceCount=1;
    close();
  }
  public synchronized void incReferenceCount(){
    referenceCount++;
  }
  public static int getThreadLocalReferenceCount(){
    return threadLocalReferenceCount;
  }
  public static synchronized void incThreadLocalReferenceCount(){
    threadLocalReferenceCount++;
  }
  public static synchronized void decThreadLocalReferenceCount(){
    threadLocalReferenceCount--;
  }
  public static boolean getNoComparators(){
    return noComparators;
  }
  /** 
 * Invoke a checkpoint programatically. Note that only one checkpoint may
 * run at a time.
 */
  public boolean invokeCheckpoint(  CheckpointConfig config,  boolean flushAll,  String invokingSource) throws DatabaseException {
    if (checkpointer != null) {
      checkpointer.doCheckpoint(config,flushAll,invokingSource);
      return true;
    }
 else {
      return false;
    }
  }
  public int invokeCleaner() throws DatabaseException {
    if (cleaner != null) {
      return cleaner.doClean(true,false);
    }
 else {
      return 0;
    }
  }
  private void requestShutdownDaemons(){
    closing=true;
    this.hook331();
    this.hook334();
    this.hook327();
  }
  /** 
 * Ask all daemon threads to shut down.
 */
  private void shutdownDaemons() throws InterruptedException {
    shutdownCheckpointer();
  }
  void shutdownCheckpointer() throws InterruptedException {
    if (checkpointer != null) {
      this.hook328();
      checkpointer=null;
    }
    return;
  }
  public boolean isNoLocking(){
    return isNoLocking;
  }
  public boolean isTransactional(){
    return isTransactional;
  }
  public boolean isReadOnly(){
    return isReadOnly;
  }
  public DatabaseImpl createDb(  Locker locker,  String databaseName,  DatabaseConfig dbConfig,  Database databaseHandle) throws DatabaseException {
    return dbMapTree.createDb(locker,databaseName,dbConfig,databaseHandle);
  }
  /** 
 * Get a database object given a database name.
 * @param databaseNametarget database.
 * @return null if database doesn't exist.
 */
  public DatabaseImpl getDb(  Locker locker,  String databaseName,  Database databaseHandle) throws DatabaseException {
    return dbMapTree.getDb(locker,databaseName,databaseHandle);
  }
  public List getDbNames() throws DatabaseException {
    return dbMapTree.getDbNames();
  }
  /** 
 * For debugging.
 */
  public void dumpMapTree() throws DatabaseException {
    dbMapTree.dump();
  }
  /** 
 * Transactional services.
 */
  public Txn txnBegin(  Transaction parent,  TransactionConfig txnConfig) throws DatabaseException {
    if (!isTransactional) {
      throw new DatabaseException("beginTransaction called, " + " but Environment was not opened " + "with transactional cpabilities");
    }
    return txnManager.txnBegin(parent,txnConfig);
  }
  public LogManager getLogManager(){
    return logManager;
  }
  public FileManager getFileManager(){
    return fileManager;
  }
  public DbTree getDbMapTree(){
    return dbMapTree;
  }
  /** 
 * Returns the config manager for the current base configuration.
 * <p>
 * The configuration can change, but changes are made by replacing the
 * config manager object with a enw one. To use a consistent set of
 * properties, call this method once and query the returned manager
 * repeatedly for each property, rather than getting the config manager via
 * this method for each property individually.
 * </p>
 */
  public DbConfigManager getConfigManager(){
    return configManager;
  }
  /** 
 * Clones the current configuration.
 */
  public EnvironmentConfig cloneConfig(){
    return DbInternal.cloneConfig(configManager.getEnvironmentConfig());
  }
  /** 
 * Clones the current mutable configuration.
 */
  public EnvironmentMutableConfig cloneMutableConfig(){
    return DbInternal.cloneMutableConfig(configManager.getEnvironmentConfig());
  }
  /** 
 * Throws an exception if an immutable property is changed.
 */
  public void checkImmutablePropsForEquality(  EnvironmentConfig config) throws IllegalArgumentException {
    DbInternal.checkImmutablePropsForEquality(configManager.getEnvironmentConfig(),config);
  }
  /** 
 * Changes the mutable config properties that are present in the given
 * config, and notifies all config observer.
 */
  public synchronized void setMutableConfig(  EnvironmentMutableConfig config) throws DatabaseException {
    EnvironmentConfig newConfig=DbInternal.cloneConfig(configManager.getEnvironmentConfig());
    DbInternal.copyMutablePropsTo(config,newConfig);
    configManager=new DbConfigManager(newConfig);
    for (int i=configObservers.size() - 1; i >= 0; i-=1) {
      EnvConfigObserver o=(EnvConfigObserver)configObservers.get(i);
      o.envConfigUpdate(configManager);
    }
  }
  /** 
 * Adds an observer of mutable config changes.
 */
  public synchronized void addConfigObserver(  EnvConfigObserver o){
    configObservers.add(o);
  }
  /** 
 * Removes an observer of mutable config changes.
 */
  public synchronized void removeConfigObserver(  EnvConfigObserver o){
    configObservers.remove(o);
  }
  public INList getInMemoryINs(){
    return inMemoryINs;
  }
  public TxnManager getTxnManager(){
    return txnManager;
  }
  public Checkpointer getCheckpointer(){
    return checkpointer;
  }
  public Cleaner getCleaner(){
    return cleaner;
  }
  public MemoryBudget getMemoryBudget(){
    return memoryBudget;
  }
  /** 
 * Info about the last recovery
 */
  public RecoveryInfo getLastRecoveryInfo(){
    return lastRecoveryInfo;
  }
  /** 
 * Get the environment home directory.
 */
  public File getEnvironmentHome(){
    return envHome;
  }
  public long getTxnTimeout(){
    return txnTimeout;
  }
  public long getLockTimeout(){
    return lockTimeout;
  }
  /** 
 * For stress testing. Should only ever be called from an assert.
 */
  public static boolean maybeForceYield(){
    if (forcedYield) {
      Thread.yield();
    }
    return true;
  }
@MethodObject static class EnvironmentImpl_createDaemons {
    EnvironmentImpl_createDaemons(    EnvironmentImpl _this){
      this._this=_this;
    }
    void execute() throws DatabaseException {
      checkpointerWakeupTime=0;
      this.hook329();
      _this.checkpointer=new Checkpointer(_this,checkpointerWakeupTime,"Checkpointer");
      this.hook332();
      _this.cleaner=new Cleaner(_this,"Cleaner");
    }
    protected EnvironmentImpl _this;
    protected long checkpointerWakeupTime;
    protected long compressorWakeupInterval;
    protected void hook329() throws DatabaseException {
    }
    protected void hook332() throws DatabaseException {
    }
  }
  protected void hook317(  DbConfigManager mgr) throws DatabaseException {
  }
  protected void hook318() throws DatabaseException {
  }
  protected void hook319() throws DatabaseException {
  }
  protected void hook320() throws DatabaseException {
  }
  protected void hook321() throws DatabaseException {
    logManager=new SyncedLogManager(this,isReadOnly);
  }
  protected void hook322() throws DatabaseException {
  }
  protected void hook323() throws DatabaseException {
  }
  protected void hook324(  long rootLsn) throws DatabaseException {
    mapTreeRootLsn=rootLsn;
  }
  protected void hook325(  StringBuffer errors) throws DatabaseException {
  }
  protected void hook326(  DbConfigManager mgr) throws DatabaseException {
  }
  protected void hook327(){
  }
  protected void hook328() throws InterruptedException {
  }
  protected void hook330(  DbConfigManager mgr) throws DatabaseException {
  }
  protected void hook331(){
  }
  protected void hook333(  DbConfigManager mgr) throws DatabaseException {
  }
  protected void hook334(){
  }
  protected void hook335() throws DatabaseException {
  }
  protected void hook336(  File envHome) throws DatabaseException {
  }
  protected void hook337() throws DatabaseException {
  }
}
