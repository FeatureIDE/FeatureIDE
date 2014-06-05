package com.sleepycat.je;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated via
 * the doc templates in the doc_src directory.
 */
public class SecondaryConfig extends DatabaseConfig {
  static SecondaryConfig DEFAULT=new SecondaryConfig();
  private boolean allowPopulate;
  private SecondaryKeyCreator keyCreator;
  private SecondaryMultiKeyCreator multiKeyCreator;
  private Database foreignKeyDatabase;
  private ForeignKeyDeleteAction foreignKeyDeleteAction=ForeignKeyDeleteAction.ABORT;
  private ForeignKeyNullifier foreignKeyNullifier;
  private ForeignMultiKeyNullifier foreignMultiKeyNullifier;
  private boolean immutableSecondaryKey;
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public SecondaryConfig(){
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setKeyCreator(  SecondaryKeyCreator keyCreator){
    this.keyCreator=keyCreator;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public SecondaryKeyCreator getKeyCreator(){
    return keyCreator;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setMultiKeyCreator(  SecondaryMultiKeyCreator multiKeyCreator){
    this.multiKeyCreator=multiKeyCreator;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public SecondaryMultiKeyCreator getMultiKeyCreator(){
    return multiKeyCreator;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setAllowPopulate(  boolean allowPopulate){
    this.allowPopulate=allowPopulate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getAllowPopulate(){
    return allowPopulate;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setForeignKeyDatabase(  Database foreignKeyDatabase){
    this.foreignKeyDatabase=foreignKeyDatabase;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public Database getForeignKeyDatabase(){
    return foreignKeyDatabase;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setForeignKeyDeleteAction(  ForeignKeyDeleteAction foreignKeyDeleteAction){
    DatabaseUtil.checkForNullParam(foreignKeyDeleteAction,"foreignKeyDeleteAction");
    this.foreignKeyDeleteAction=foreignKeyDeleteAction;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public ForeignKeyDeleteAction getForeignKeyDeleteAction(){
    return foreignKeyDeleteAction;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setForeignKeyNullifier(  ForeignKeyNullifier foreignKeyNullifier){
    this.foreignKeyNullifier=foreignKeyNullifier;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public ForeignKeyNullifier getForeignKeyNullifier(){
    return foreignKeyNullifier;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setForeignMultiKeyNullifier(  ForeignMultiKeyNullifier foreignMultiKeyNullifier){
    this.foreignMultiKeyNullifier=foreignMultiKeyNullifier;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public ForeignMultiKeyNullifier getForeignMultiKeyNullifier(){
    return foreignMultiKeyNullifier;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void setImmutableSecondaryKey(  boolean immutableSecondaryKey){
    this.immutableSecondaryKey=immutableSecondaryKey;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean getImmutableSecondaryKey(){
    return immutableSecondaryKey;
  }
  void validate(  DatabaseConfig configArg) throws DatabaseException {
    super.validate(configArg);
    if (configArg == null || !(configArg instanceof SecondaryConfig)) {
      throw new DatabaseException("The SecondaryConfig argument is null.");
    }
    SecondaryConfig config=(SecondaryConfig)configArg;
    boolean kcMatch=equalOrBothNull(config.getKeyCreator(),keyCreator);
    boolean mkcMatch=equalOrBothNull(config.getMultiKeyCreator(),multiKeyCreator);
    boolean fkdMatch=(config.getForeignKeyDatabase() == foreignKeyDatabase);
    boolean fkdaMatch=(config.getForeignKeyDeleteAction() == foreignKeyDeleteAction);
    boolean fknMatch=equalOrBothNull(config.getForeignKeyNullifier(),foreignKeyNullifier);
    boolean fmknMatch=equalOrBothNull(config.getForeignMultiKeyNullifier(),foreignMultiKeyNullifier);
    boolean imskMatch=(config.getImmutableSecondaryKey() == immutableSecondaryKey);
    if (kcMatch && mkcMatch && fkdMatch&& fkdaMatch&& fknMatch&& fmknMatch&& imskMatch) {
      return;
    }
    String message=genSecondaryConfigMismatchMessage(config,kcMatch,mkcMatch,fkdMatch,fkdaMatch,fknMatch,fmknMatch,imskMatch);
    throw new DatabaseException(message);
  }
  private boolean equalOrBothNull(  Object o1,  Object o2){
    return (o1 != null) ? o1.equals(o2) : (o2 == null);
  }
  String genSecondaryConfigMismatchMessage(  DatabaseConfig config,  boolean kcMatch,  boolean mkcMatch,  boolean fkdMatch,  boolean fkdaMatch,  boolean fknMatch,  boolean fmknMatch,  boolean imskMatch){
    StringBuffer ret=new StringBuffer("The following SecondaryConfig parameters for the\n" + "cached Database do not match the parameters for the\n" + "requested Database:\n");
    if (!kcMatch) {
      ret.append(" SecondaryKeyCreator\n");
    }
    if (!mkcMatch) {
      ret.append(" SecondaryMultiKeyCreator\n");
    }
    if (!fkdMatch) {
      ret.append(" ForeignKeyDelete\n");
    }
    if (!fkdaMatch) {
      ret.append(" ForeignKeyDeleteAction\n");
    }
    if (!fknMatch) {
      ret.append(" ForeignKeyNullifier\n");
    }
    if (!fknMatch) {
      ret.append(" ForeignMultiKeyNullifier\n");
    }
    if (!imskMatch) {
      ret.append(" ImmutableSecondaryKey\n");
    }
    return ret.toString();
  }
}
