package com.sleepycat.je.util;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Date;
import java.util.logging.Level;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.Environment;
import com.sleepycat.je.EnvironmentConfig;
import com.sleepycat.je.JEVersion;
import com.sleepycat.je.OperationStatus;
import com.sleepycat.je.utilint.CmdUtil;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
public class DbLoad {
  private static final boolean DEBUG=false;
  protected Environment env;
  private boolean formatUsingPrintable;
  private String dbName;
  private BufferedReader reader;
  private boolean noOverwrite;
  private boolean textFileMode;
  private boolean dupSort;
  private boolean ignoreUnknownConfig;
  private boolean commandLine;
  private long progressInterval;
  private long totalLoadBytes;
  private static final String usageString="usage: " + CmdUtil.getJavaCommand(DbLoad.class) + "\n"+ "       -h <dir>             # environment home directory\n"+ "       [-f <fileName>]      # input file\n"+ "       [-n ]                # no overwrite mode\n"+ "       [-T]                 # input file is in text mode\n"+ "       [-I]                 # ignore unknown parameters\n"+ "       [-c name=value]      # config values\n"+ "       [-s <databaseName> ] # database to load\n"+ "       [-v]                 # show progress\n"+ "       [-V]                 # print JE version number";
  static public void main(  String argv[]) throws DatabaseException, IOException {
    DbLoad loader=parseArgs(argv);
    try {
      loader.load();
    }
 catch (    Throwable e) {
      e.printStackTrace();
    }
    loader.env.close();
  }
  static private void printUsage(  String msg){
    System.err.println(msg);
    System.err.println(usageString);
    System.exit(-1);
  }
  static private DbLoad parseArgs(  String argv[]) throws IOException, DatabaseException {
    boolean noOverwrite=false;
    boolean textFileMode=false;
    boolean ignoreUnknownConfig=false;
    boolean showProgressInterval=false;
    int argc=0;
    int nArgs=argv.length;
    String inputFileName=null;
    File envHome=null;
    String dbName=null;
    long progressInterval=0;
    DbLoad ret=new DbLoad();
    ret.setCommandLine(true);
    while (argc < nArgs) {
      String thisArg=argv[argc++].trim();
      if (thisArg.equals("-n")) {
        noOverwrite=true;
      }
 else       if (thisArg.equals("-T")) {
        textFileMode=true;
      }
 else       if (thisArg.equals("-I")) {
        ignoreUnknownConfig=true;
      }
 else       if (thisArg.equals("-V")) {
        System.out.println(JEVersion.CURRENT_VERSION);
        System.exit(0);
      }
 else       if (thisArg.equals("-f")) {
        if (argc < nArgs) {
          inputFileName=argv[argc++];
        }
 else {
          printUsage("-f requires an argument");
        }
      }
 else       if (thisArg.equals("-h")) {
        if (argc < nArgs) {
          envHome=new File(argv[argc++]);
        }
 else {
          printUsage("-h requires an argument");
        }
      }
 else       if (thisArg.equals("-s")) {
        if (argc < nArgs) {
          dbName=argv[argc++];
        }
 else {
          printUsage("-s requires an argument");
        }
      }
 else       if (thisArg.equals("-c")) {
        if (argc < nArgs) {
          try {
            ret.loadConfigLine(argv[argc++]);
          }
 catch (          IllegalArgumentException e) {
            printUsage("-c: " + e.getMessage());
          }
        }
 else {
          printUsage("-c requires an argument");
        }
      }
 else       if (thisArg.equals("-v")) {
        showProgressInterval=true;
      }
    }
    if (envHome == null) {
      printUsage("-h is a required argument");
    }
    long totalLoadBytes=0;
    InputStream is;
    if (inputFileName == null) {
      is=System.in;
      if (showProgressInterval) {
        printUsage("-v requires -f");
      }
    }
 else {
      is=new FileInputStream(inputFileName);
      if (showProgressInterval) {
        totalLoadBytes=((FileInputStream)is).getChannel().size();
        progressInterval=totalLoadBytes / 20;
      }
    }
    BufferedReader reader=new BufferedReader(new InputStreamReader(is));
    EnvironmentConfig envConfig=new EnvironmentConfig();
    envConfig.setAllowCreate(true);
    Environment env=new Environment(envHome,envConfig);
    ret.setEnv(env);
    ret.setDbName(dbName);
    ret.setInputReader(reader);
    ret.setNoOverwrite(noOverwrite);
    ret.setTextFileMode(textFileMode);
    ret.setIgnoreUnknownConfig(ignoreUnknownConfig);
    ret.setProgressInterval(progressInterval);
    ret.setTotalLoadBytes(totalLoadBytes);
    return ret;
  }
  public DbLoad(){
  }
  /** 
 * If true, enables output of warning messages.  Command line behavior is
 * not available via the public API.
 */
  private void setCommandLine(  boolean commandLine){
    this.commandLine=commandLine;
  }
  public void setEnv(  Environment env){
    this.env=env;
  }
  public void setDbName(  String dbName){
    this.dbName=dbName;
  }
  public void setInputReader(  BufferedReader reader){
    this.reader=reader;
  }
  public void setNoOverwrite(  boolean noOverwrite){
    this.noOverwrite=noOverwrite;
  }
  public void setTextFileMode(  boolean textFileMode){
    this.textFileMode=textFileMode;
  }
  public void setIgnoreUnknownConfig(  boolean ignoreUnknownConfigMode){
    this.ignoreUnknownConfig=ignoreUnknownConfigMode;
  }
  public void setProgressInterval(  long progressInterval){
    this.progressInterval=progressInterval;
  }
  public void setTotalLoadBytes(  long totalLoadBytes){
    this.totalLoadBytes=totalLoadBytes;
  }
  public boolean load() throws IOException, DatabaseException {
    if (progressInterval > 0) {
      System.out.println("Load start: " + new Date());
    }
    if (textFileMode) {
      formatUsingPrintable=true;
    }
 else {
      loadHeader();
    }
    if (dbName == null) {
      throw new IllegalArgumentException("Must supply a database name if -l not supplied.");
    }
    DatabaseConfig dbConfig=new DatabaseConfig();
    dbConfig.setSortedDuplicates(dupSort);
    dbConfig.setAllowCreate(true);
    Database db=env.openDatabase(null,dbName,dbConfig);
    loadData(db);
    db.close();
    this.hook835();
    if (progressInterval > 0) {
      System.out.println("Load end: " + new Date());
    }
    return true;
  }
  private void loadConfigLine(  String line) throws DatabaseException {
    int equalsIdx=line.indexOf('=');
    if (equalsIdx < 0) {
      throw new IllegalArgumentException("Invalid header parameter: " + line);
    }
    String keyword=line.substring(0,equalsIdx).trim().toLowerCase();
    String value=line.substring(equalsIdx + 1).trim();
    if (keyword.equals("version")) {
      if (DEBUG) {
        System.out.println("Found version: " + line);
      }
      if (!value.equals("3")) {
        throw new IllegalArgumentException("Version " + value + " is not supported.");
      }
    }
 else     if (keyword.equals("format")) {
      value=value.toLowerCase();
      if (value.equals("print")) {
        formatUsingPrintable=true;
      }
 else       if (value.equals("bytevalue")) {
        formatUsingPrintable=false;
      }
 else {
        throw new IllegalArgumentException(value + " is an unknown value for the format keyword");
      }
      if (DEBUG) {
        System.out.println("Found format: " + formatUsingPrintable);
      }
    }
 else     if (keyword.equals("dupsort")) {
      value=value.toLowerCase();
      if (value.equals("true") || value.equals("1")) {
        dupSort=true;
      }
 else       if (value.equals("false") || value.equals("0")) {
        dupSort=false;
      }
 else {
        throw new IllegalArgumentException(value + " is an unknown value for the dupsort keyword");
      }
      if (DEBUG) {
        System.out.println("Found dupsort: " + dupSort);
      }
    }
 else     if (keyword.equals("type")) {
      value=value.toLowerCase();
      if (!value.equals("btree")) {
        throw new IllegalArgumentException(value + " is not a supported database type.");
      }
      if (DEBUG) {
        System.out.println("Found type: " + line);
      }
    }
 else     if (keyword.equals("database")) {
      if (dbName == null) {
        dbName=value;
      }
      if (DEBUG) {
        System.out.println("DatabaseImpl: " + dbName);
      }
    }
 else     if (!ignoreUnknownConfig) {
      throw new IllegalArgumentException("'" + line + "' is not understood.");
    }
  }
  private void loadHeader() throws IOException, DatabaseException {
    if (DEBUG) {
      System.out.println("loading header");
    }
    String line=reader.readLine();
    while (line != null && !line.equals("HEADER=END")) {
      loadConfigLine(line);
      line=reader.readLine();
    }
  }
  private void loadData(  Database db) throws DatabaseException, IOException {
    String keyLine=reader.readLine();
    String dataLine=null;
    int count=0;
    long totalBytesRead=0;
    long lastTime=System.currentTimeMillis();
    long bytesReadThisInterval=0;
    while (keyLine != null && !keyLine.equals("DATA=END")) {
      dataLine=reader.readLine();
      if (dataLine == null) {
        throw new DatabaseException("No data to match key " + keyLine);
      }
      bytesReadThisInterval+=dataLine.length() + 1;
      byte[] keyBytes=loadLine(keyLine.trim());
      byte[] dataBytes=loadLine(dataLine.trim());
      DatabaseEntry key=new DatabaseEntry(keyBytes);
      DatabaseEntry data=new DatabaseEntry(dataBytes);
      if (noOverwrite) {
        if (db.putNoOverwrite(null,key,data) == OperationStatus.KEYEXIST) {
          if (commandLine) {
            System.err.println("Key exists: " + key);
          }
        }
      }
 else {
        db.put(null,key,data);
      }
      count++;
      if ((progressInterval > 0) && (bytesReadThisInterval > progressInterval)) {
        totalBytesRead+=bytesReadThisInterval;
        bytesReadThisInterval-=progressInterval;
        long now=System.currentTimeMillis();
        System.out.println("loaded " + count + " records  "+ (now - lastTime)+ " ms - % completed: "+ ((100 * totalBytesRead) / totalLoadBytes));
        lastTime=now;
      }
      keyLine=reader.readLine();
      if (keyLine == null) {
        throw new DatabaseException("No \"DATA=END\"");
      }
      bytesReadThisInterval+=keyLine.length() + 1;
    }
  }
  private byte[] loadLine(  String line) throws DatabaseException {
    if (formatUsingPrintable) {
      return readPrintableLine(line);
    }
    int nBytes=line.length() / 2;
    byte[] ret=new byte[nBytes];
    int charIdx=0;
    for (int i=0; i < nBytes; i++, charIdx+=2) {
      int b2=Character.digit(line.charAt(charIdx),16);
      b2<<=4;
      b2+=Character.digit(line.charAt(charIdx + 1),16);
      ret[i]=(byte)b2;
    }
    return ret;
  }
  static private byte backSlashValue=(byte)(new Character('\\').charValue() & 0xff);
  private byte[] readPrintableLine(  String line) throws DatabaseException {
    int maxNBytes=line.length();
    byte[] ba=new byte[maxNBytes];
    int actualNBytes=0;
    for (int charIdx=0; charIdx < maxNBytes; charIdx++) {
      char c=line.charAt(charIdx);
      if (c == '\\') {
        if (++charIdx < maxNBytes) {
          char c1=line.charAt(charIdx);
          if (c1 == '\\') {
            ba[actualNBytes++]=backSlashValue;
          }
 else {
            if (++charIdx < maxNBytes) {
              char c2=line.charAt(charIdx);
              int b=Character.digit(c1,16);
              b<<=4;
              b+=Character.digit(c2,16);
              ba[actualNBytes++]=(byte)b;
            }
 else {
              throw new DatabaseException("Corrupted file");
            }
          }
        }
 else {
          throw new DatabaseException("Corrupted file");
        }
      }
 else {
        ba[actualNBytes++]=(byte)(c & 0xff);
      }
    }
    if (maxNBytes == actualNBytes) {
      return ba;
    }
 else {
      byte[] ret=new byte[actualNBytes];
      System.arraycopy(ba,0,ret,0,actualNBytes);
      return ret;
    }
  }
  protected void hook835() throws IOException, DatabaseException {
  }
}
