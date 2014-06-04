package com.sleepycat.je;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Properties;
import com.sleepycat.je.config.ConfigParam;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class EnvironmentMutableConfig implements Cloneable {
  private boolean txnNoSync=false;
  private boolean txnWriteNoSync=false;
  protected long cacheSize;
  /** 
 * Note that in the implementation we choose not to extend Properties 
 * in order to keep the configuration type safe.
 */
  private Properties props;
  /** 
 * For unit testing, to prevent loading of je.properties.
 */
  private boolean loadPropertyFile=true;
  /** 
 * Internal boolean that says whether or not to validate params.  Setting
 * it to false means that parameter value validatation won't be performed
 * during setVal() calls.  Only should be set to false by unit tests using
 * DbInternal.
 */
  private boolean validateParams=true;
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public EnvironmentMutableConfig(){
    props=new Properties();
  }
  /** 
 * Used by EnvironmentConfig to construct from properties.
 */
  EnvironmentMutableConfig(  Properties properties) throws IllegalArgumentException {
    validateProperties(properties);
    props=new Properties();
    props.putAll(properties);
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setTxnNoSync(  boolean noSync){
    txnNoSync=noSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getTxnNoSync(){
    return txnNoSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setTxnWriteNoSync(  boolean writeNoSync){
    txnWriteNoSync=writeNoSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getTxnWriteNoSync(){
    return txnWriteNoSync;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setCacheSize(  long totalBytes) throws IllegalArgumentException {
    setVal(EnvironmentParams.MAX_MEMORY,Long.toString(totalBytes));
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getCacheSize(){
    return cacheSize;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setCachePercent(  int percent) throws IllegalArgumentException {
    setVal(EnvironmentParams.MAX_MEMORY_PERCENT,Integer.toString(percent));
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getCachePercent(){
    String val=getVal(EnvironmentParams.MAX_MEMORY_PERCENT);
    try {
      return Integer.parseInt(val);
    }
 catch (    NumberFormatException e) {
      throw new IllegalArgumentException("Cache percent is not a valid integer: " + e.getMessage());
    }
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setConfigParam(  String paramName,  String value) throws IllegalArgumentException {
    ConfigParam param=(ConfigParam)EnvironmentParams.SUPPORTED_PARAMS.get(paramName);
    if (param == null) {
      throw new IllegalArgumentException(paramName + " is not a valid BDBJE environment configuration");
    }
    if (!param.isMutable()) {
      throw new IllegalArgumentException(paramName + " is not a mutable BDBJE environment configuration");
    }
    setVal(param,value);
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public String getConfigParam(  String paramName) throws IllegalArgumentException {
    ConfigParam param=(ConfigParam)EnvironmentParams.SUPPORTED_PARAMS.get(paramName);
    if (param == null) {
      throw new IllegalArgumentException(paramName + " is not a valid BDBJE environment configuration");
    }
    return getVal(param);
  }
  /** 
 * Gets either the value stored in this configuration or the
 * default value for this param.
 */
  String getVal(  ConfigParam param){
    String val=props.getProperty(param.getName());
    if (val == null) {
      val=param.getDefault();
    }
    return val;
  }
  /** 
 * Sets and validates the specified parameter.
 */
  void setVal(  ConfigParam param,  String val) throws IllegalArgumentException {
    if (validateParams) {
      param.validateValue(val);
    }
    props.setProperty(param.getName(),val);
  }
  void setValidateParams(  boolean validateParams){
    this.validateParams=validateParams;
  }
  /** 
 * Validate a property bag passed in a construction time.
 */
  void validateProperties(  Properties props) throws IllegalArgumentException {
    Enumeration propNames=props.propertyNames();
    while (propNames.hasMoreElements()) {
      String name=(String)propNames.nextElement();
      ConfigParam param=(ConfigParam)EnvironmentParams.SUPPORTED_PARAMS.get(name);
      if (param == null) {
        throw new IllegalArgumentException(name + " is not a valid BDBJE environment configuration");
      }
      param.validateValue(props.getProperty(name));
    }
  }
  /** 
 * Check that the immutable values in the environment config used to open
 * an environment match those in the config object saved by the underlying
 * shared EnvironmentImpl.
 */
  void checkImmutablePropsForEquality(  EnvironmentMutableConfig passedConfig) throws IllegalArgumentException {
    Properties passedProps=passedConfig.props;
    Iterator iter=EnvironmentParams.SUPPORTED_PARAMS.keySet().iterator();
    while (iter.hasNext()) {
      String paramName=(String)iter.next();
      ConfigParam param=(ConfigParam)EnvironmentParams.SUPPORTED_PARAMS.get(paramName);
      assert param != null;
      if (!param.isMutable()) {
        String paramVal=props.getProperty(paramName);
        String useParamVal=passedProps.getProperty(paramName);
        if ((paramVal != null) ? (!paramVal.equals(useParamVal)) : (useParamVal != null)) {
          throw new IllegalArgumentException(paramName + " is set to " + useParamVal+ " in the config parameter"+ " which is incompatible"+ " with the value of "+ paramVal+ " in the"+ " underlying environment");
        }
      }
    }
  }
  /** 
 * Overrides Object.clone() to clone all properties, used by this class and
 * EnvironmentConfig.
 */
  protected Object clone() throws CloneNotSupportedException {
    EnvironmentMutableConfig copy=(EnvironmentMutableConfig)super.clone();
    copy.props=(Properties)props.clone();
    return copy;
  }
  /** 
 * Used by Environment to create a copy of the application
 * supplied configuration. Done this way to provide non-public cloning.
 */
  EnvironmentMutableConfig cloneMutableConfig(){
    try {
      EnvironmentMutableConfig copy=(EnvironmentMutableConfig)clone();
      copy.clearImmutableProps();
      return copy;
    }
 catch (    CloneNotSupportedException willNeverOccur) {
      return null;
    }
  }
  /** 
 * Copies the per-handle properties of this object to the given config
 * object.
 */
  void copyHandlePropsTo(  EnvironmentMutableConfig other){
    other.txnNoSync=txnNoSync;
    other.txnWriteNoSync=txnWriteNoSync;
  }
  /** 
 * Copies all mutable props to the given config object.
 */
  void copyMutablePropsTo(  EnvironmentMutableConfig toConfig){
    Properties toProps=toConfig.props;
    Enumeration propNames=props.propertyNames();
    while (propNames.hasMoreElements()) {
      String paramName=(String)propNames.nextElement();
      ConfigParam param=(ConfigParam)EnvironmentParams.SUPPORTED_PARAMS.get(paramName);
      assert param != null;
      if (param.isMutable()) {
        String newVal=props.getProperty(paramName);
        toProps.setProperty(paramName,newVal);
      }
    }
  }
  /** 
 * Fill in the properties calculated by the environment to the given
 * config object.
 */
  void fillInEnvironmentGeneratedProps(  EnvironmentImpl envImpl){
    cacheSize=envImpl.getMemoryBudget().getMaxMemory();
  }
  /** 
 * Removes all immutable props.
 */
  private void clearImmutableProps(){
    Enumeration propNames=props.propertyNames();
    while (propNames.hasMoreElements()) {
      String paramName=(String)propNames.nextElement();
      ConfigParam param=(ConfigParam)EnvironmentParams.SUPPORTED_PARAMS.get(paramName);
      assert param != null;
      if (!param.isMutable()) {
        props.remove(paramName);
      }
    }
  }
  /** 
 * For unit testing, to prevent loading of je.properties.
 */
  void setLoadPropertyFile(  boolean loadPropertyFile){
    this.loadPropertyFile=loadPropertyFile;
  }
  /** 
 * For unit testing, to prevent loading of je.properties.
 */
  boolean getLoadPropertyFile(){
    return loadPropertyFile;
  }
  /** 
 * Testing support
 */
  int getNumExplicitlySetParams(){
    return props.size();
  }
  public String toString(){
    return props.toString();
  }
}
