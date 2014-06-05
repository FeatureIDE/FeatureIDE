package com.sleepycat.je;
import java.util.Comparator;
import com.sleepycat.je.dbi.DatabaseImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class DatabaseConfig implements Cloneable {
  public static final DatabaseConfig DEFAULT=new DatabaseConfig();
  private boolean allowCreate=false;
  private boolean exclusiveCreate=false;
  private boolean transactional=false;
  private boolean readOnly=false;
  private boolean duplicatesAllowed=false;
  private int nodeMax;
  private int nodeMaxDupTree;
  private Comparator btreeComparator=null;
  private Comparator duplicateComparator=null;
  private boolean overrideBtreeComparator=false;
  private boolean overrideDupComparator=false;
  private boolean useExistingConfig=false;
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public DatabaseConfig(){
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setAllowCreate(  boolean allowCreate){
    this.allowCreate=allowCreate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getAllowCreate(){
    return allowCreate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setExclusiveCreate(  boolean exclusiveCreate){
    this.exclusiveCreate=exclusiveCreate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getExclusiveCreate(){
    return exclusiveCreate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setSortedDuplicates(  boolean duplicatesAllowed){
    this.duplicatesAllowed=duplicatesAllowed;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getSortedDuplicates(){
    return duplicatesAllowed;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setTransactional(  boolean transactional){
    this.transactional=transactional;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getTransactional(){
    return transactional;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setReadOnly(  boolean readOnly){
    this.readOnly=readOnly;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getReadOnly(){
    return readOnly;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setNodeMaxEntries(  int nodeMaxEntries){
    this.nodeMax=nodeMaxEntries;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setNodeMaxDupTreeEntries(  int nodeMaxDupTreeEntries){
    this.nodeMaxDupTree=nodeMaxDupTreeEntries;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNodeMaxEntries(){
    return nodeMax;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNodeMaxDupTreeEntries(){
    return nodeMaxDupTree;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setBtreeComparator(  Class btreeComparator){
    this.btreeComparator=validateComparator(btreeComparator,"Btree");
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public Comparator getBtreeComparator(){
    return btreeComparator;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setOverrideBtreeComparator(  boolean override){
    overrideBtreeComparator=override;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getOverrideBtreeComparator(){
    return overrideBtreeComparator;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setDuplicateComparator(  Class duplicateComparator){
    this.duplicateComparator=validateComparator(duplicateComparator,"Duplicate");
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public Comparator getDuplicateComparator(){
    return duplicateComparator;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setOverrideDuplicateComparator(  boolean override){
    overrideDupComparator=override;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getOverrideDuplicateComparator(){
    return overrideDupComparator;
  }
  /** 
 * For utilities, to avoid having to know the configuration of a database.
 */
  void setUseExistingConfig(  boolean useExistingConfig){
    this.useExistingConfig=useExistingConfig;
  }
  /** 
 * For utilities, to avoid having to know the configuration of a database.
 */
  boolean getUseExistingConfig(){
    return useExistingConfig;
  }
  /** 
 * Used by Database to create a copy of the application
 * supplied configuration. Done this way to provide non-public cloning.
 */
  DatabaseConfig cloneConfig(){
    try {
      return (DatabaseConfig)super.clone();
    }
 catch (    CloneNotSupportedException willNeverOccur) {
      return null;
    }
  }
  void validate(  DatabaseConfig config) throws DatabaseException {
    if (config == null) {
      config=DatabaseConfig.DEFAULT;
    }
    boolean txnMatch=config.getTransactional() == transactional;
    boolean roMatch=config.getReadOnly() == readOnly;
    boolean sdMatch=config.getSortedDuplicates() == duplicatesAllowed;
    boolean btCmpMatch=(config.overrideBtreeComparator ? btreeComparator.getClass() == config.getBtreeComparator().getClass() : true);
    boolean dtCmpMatch=(config.getOverrideDuplicateComparator() ? duplicateComparator.getClass() == config.getDuplicateComparator().getClass() : true);
    if (txnMatch && roMatch && sdMatch&& btCmpMatch&& dtCmpMatch) {
      return;
    }
 else {
      String message=genDatabaseConfigMismatchMessage(config,txnMatch,roMatch,sdMatch,btCmpMatch,dtCmpMatch);
      throw new DatabaseException(message);
    }
  }
  String genDatabaseConfigMismatchMessage(  DatabaseConfig config,  boolean txnMatch,  boolean roMatch,  boolean sdMatch,  boolean btCmpMatch,  boolean dtCmpMatch){
    StringBuffer ret=new StringBuffer("The following DatabaseConfig parameters for the\n" + "cached Database do not match the parameters for the\n" + "requested Database:\n");
    if (!txnMatch) {
      ret.append(" Transactional\n");
    }
    if (!roMatch) {
      ret.append(" Read-Only\n");
    }
    if (!sdMatch) {
      ret.append(" Sorted Duplicates\n");
    }
    if (!btCmpMatch) {
      ret.append(" Btree Comparator\n");
    }
    if (!dtCmpMatch) {
      ret.append(" Duplicate Comparator\n");
    }
    return ret.toString();
  }
  /** 
 * Check that this comparator can be instantiated by JE.
 */
  private Comparator validateComparator(  Class comparator,  String type) throws IllegalArgumentException {
    if (comparator == null) {
      return null;
    }
    try {
      Comparator ret=DatabaseImpl.instantiateComparator(comparator,type);
      if (ret instanceof Comparator) {
        return ret;
      }
 else {
        throw new IllegalArgumentException(comparator.getName() + " is is not valid as a " + type+ " comparator because it does not "+ " implement java.util.Comparator.");
      }
    }
 catch (    DatabaseException e) {
      throw new IllegalArgumentException(type + " comparator is not valid: " + e.getMessage()+ "\nPerhaps you have not implemented a zero-parameter "+ "constructor for the comparator or the comparator class "+ "cannot be found.");
    }
  }
}
