package com.sleepycat.je.dbi;
import java.util.Iterator;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.DBIN;
import com.sleepycat.je.tree.DIN;
import com.sleepycat.je.tree.IN;
import de.ovgu.cide.jakutil.*;
/** 
 * MemoryBudget calculates the available memory for JE and how to apportion it
 * between cache and log buffers. It is meant to centralize all memory
 * calculations. Objects that ask for memory budgets should get settings from
 * this class, rather than using the configuration parameter values directly.
 */
public class MemoryBudget implements EnvConfigObserver {
static {
    sinit();
  }
  private static void sinit(){
    new MemoryBudget_sinit().execute();
  }
  public final static long MIN_MAX_MEMORY_SIZE=96 * 1024;
  public final static String MIN_MAX_MEMORY_SIZE_STRING=Long.toString(MIN_MAX_MEMORY_SIZE);
  private final static long N_64MB=(1 << 26);
  private long maxMemory;
  private long logBufferBudget;
  private EnvironmentImpl envImpl;
  MemoryBudget(  EnvironmentImpl envImpl,  DbConfigManager configManager) throws DatabaseException {
    this.envImpl=envImpl;
    envImpl.addConfigObserver(this);
    reset(configManager);
    this.hook351(configManager);
  }
  /** 
 * Respond to config updates.
 */
  public void envConfigUpdate(  DbConfigManager configManager) throws DatabaseException {
    long oldLogBufferBudget=logBufferBudget;
    reset(configManager);
    if (oldLogBufferBudget != logBufferBudget) {
      envImpl.getLogManager().resetPool(configManager);
    }
  }
  /** 
 * Initialize at construction time and when the cache is resized.
 */
  private void reset(  DbConfigManager configManager) throws DatabaseException {
    new MemoryBudget_reset(this,configManager).execute();
  }
  /** 
 * Returns Runtime.maxMemory(), accounting for a MacOS bug. May return
 * Long.MAX_VALUE if there is no inherent limit. Used by unit tests as well
 * as by this class.
 */
  public static long getRuntimeMaxMemory(){
    if ("Mac OS X".equals(System.getProperty("os.name"))) {
      String jvmVersion=System.getProperty("java.version");
      if (jvmVersion != null && jvmVersion.startsWith("1.4.2")) {
        return Long.MAX_VALUE;
      }
    }
    return Runtime.getRuntime().maxMemory();
  }
  public long getLogBufferBudget(){
    return logBufferBudget;
  }
  public long getMaxMemory(){
    return maxMemory;
  }
@MethodObject static class MemoryBudget_sinit {
    void execute(){
      this.hook348();
    }
    protected boolean is64;
    protected boolean isJVM14;
    protected String overrideArch;
    protected String arch;
    protected RuntimeException RE;
    protected void hook348(){
    }
  }
@MethodObject static class MemoryBudget_reset {
    MemoryBudget_reset(    MemoryBudget _this,    DbConfigManager configManager){
      this._this=_this;
      this.configManager=configManager;
    }
    void execute() throws DatabaseException {
      newMaxMemory=configManager.getLong(EnvironmentParams.MAX_MEMORY);
      jvmMemory=_this.getRuntimeMaxMemory();
      if (newMaxMemory != 0) {
        if (jvmMemory < newMaxMemory) {
          throw new IllegalArgumentException(EnvironmentParams.MAX_MEMORY.getName() + " has a value of " + newMaxMemory+ " but the JVM is only configured for "+ jvmMemory+ ". Consider using je.maxMemoryPercent.");
        }
        if (newMaxMemory < _this.MIN_MAX_MEMORY_SIZE) {
          throw new IllegalArgumentException(EnvironmentParams.MAX_MEMORY.getName() + " is " + newMaxMemory+ " which is less than the minimum: "+ _this.MIN_MAX_MEMORY_SIZE);
        }
      }
 else {
        if (jvmMemory == Long.MAX_VALUE) {
          jvmMemory=_this.N_64MB;
        }
        maxMemoryPercent=configManager.getInt(EnvironmentParams.MAX_MEMORY_PERCENT);
        newMaxMemory=(maxMemoryPercent * jvmMemory) / 100;
      }
      newLogBufferBudget=configManager.getLong(EnvironmentParams.LOG_MEM_SIZE);
      if (newLogBufferBudget == 0) {
        newLogBufferBudget=newMaxMemory >> 4;
      }
 else       if (newLogBufferBudget > newMaxMemory / 2) {
        newLogBufferBudget=newMaxMemory / 2;
      }
      numBuffers=configManager.getInt(EnvironmentParams.NUM_LOG_BUFFERS);
      startingBufferSize=newLogBufferBudget / numBuffers;
      logBufferSize=configManager.getInt(EnvironmentParams.LOG_BUFFER_MAX_SIZE);
      if (startingBufferSize > logBufferSize) {
        startingBufferSize=logBufferSize;
        newLogBufferBudget=numBuffers * startingBufferSize;
      }
 else       if (startingBufferSize < EnvironmentParams.MIN_LOG_BUFFER_SIZE) {
        startingBufferSize=EnvironmentParams.MIN_LOG_BUFFER_SIZE;
        newLogBufferBudget=numBuffers * startingBufferSize;
      }
      this.hook350();
      newTrackerBudget=(newMaxMemory * _this.envImpl.getConfigManager().getInt(EnvironmentParams.CLEANER_DETAIL_MAX_MEMORY_PERCENTAGE)) / 100;
      _this.maxMemory=newMaxMemory;
      this.hook349();
      _this.logBufferBudget=newLogBufferBudget;
    }
    protected MemoryBudget _this;
    protected DbConfigManager configManager;
    protected long newMaxMemory;
    protected long jvmMemory;
    protected int maxMemoryPercent;
    protected long newLogBufferBudget;
    protected int numBuffers;
    protected long startingBufferSize;
    protected int logBufferSize;
    protected long newCriticalThreshold;
    protected long newTrackerBudget;
    protected void hook349() throws DatabaseException {
    }
    protected void hook350() throws DatabaseException {
    }
  }
  protected void hook351(  DbConfigManager configManager) throws DatabaseException {
  }
}
