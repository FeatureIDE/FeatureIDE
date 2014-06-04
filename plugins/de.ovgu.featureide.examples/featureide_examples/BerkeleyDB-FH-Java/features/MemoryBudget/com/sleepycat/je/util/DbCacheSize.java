package com.sleepycat.je.util;
import java.io.File;
import java.io.PrintStream;
import java.math.BigInteger;
import java.text.NumberFormat;
import java.util.Random;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.Environment;
import com.sleepycat.je.EnvironmentConfig;
import com.sleepycat.je.OperationStatus;
import com.sleepycat.je.dbi.MemoryBudget;
import com.sleepycat.je.utilint.CmdUtil;
import de.ovgu.cide.jakutil.*;
/** 
 * Estimating JE in-memory sizes as a function of key and data size is not
 * straightforward for two reasons. There is some fixed overhead for each btree
 * internal node, so tree fanout and degree of node sparseness impacts memory
 * consumption. In addition, JE compresses some of the internal nodes where
 * possible, but compression depends on on-disk layouts.
 * DbCacheSize is an aid for estimating cache sizes. To get an estimate of the
 * in-memory footprint for a given database, specify the number of records and
 * record characteristics and DbCacheSize will return a minimum and maximum
 * estimate of the cache size required for holding the database in memory. If
 * the user specifies the record's data size, the utility will return both
 * values for holding just the internal nodes of the btree, and for holding the
 * entire database in cache.
 * Note that "cache size" is a percentage more than "btree size", to cover
 * general environment resources like log buffers. Each invocation of the
 * utility returns an estimate for a single database in an environment. For an
 * environment with multiple databases, run the utility for each database, add
 * up the btree sizes, and then add 10 percent.
 * Note that the utility does not yet cover duplicate records and the API is
 * subject to change release to release.
 * The only required parameters are the number of records and key size. Data
 * size, non-tree cache overhead, btree fanout, and other parameters can also be
 * provided. For example:
 * $ java DbCacheSize -records 554719 -key 16 -data 100 Inputs: records=554719
 * keySize=16 dataSize=100 nodeMax=128 density=80% overhead=10%
 * Cache Size Btree Size Description -------------- -------------- -----------
 * 30,547,440 27,492,696 Minimum, internal nodes only 41,460,720 37,314,648
 * Maximum, internal nodes only 114,371,644 102,934,480 Minimum, internal nodes
 * and leaf nodes 125,284,924 112,756,432 Maximum, internal nodes and leaf nodes
 * Btree levels: 3
 * This says that the minimum cache size to hold only the internal nodes of the
 * btree in cache is approximately 30MB. The maximum size to hold the entire
 * database in cache, both internal nodes and datarecords, is 125Mb.
 */
public class DbCacheSize {
  private static final NumberFormat INT_FORMAT=NumberFormat.getIntegerInstance();
  private static final String HEADER="    Cache Size      Btree Size  Description\n" + "--------------  --------------  -----------";
  private static final int COLUMN_WIDTH=14;
  private static final int COLUMN_SEPARATOR=2;
  public static void main(  String[] args){
    try {
      long records=0;
      int keySize=0;
      int dataSize=0;
      int nodeMax=128;
      int density=80;
      long overhead=0;
      File measureDir=null;
      boolean measureRandom=false;
      for (int i=0; i < args.length; i+=1) {
        String name=args[i];
        String val=null;
        if (i < args.length - 1 && !args[i + 1].startsWith("-")) {
          i+=1;
          val=args[i];
        }
        if (name.equals("-records")) {
          if (val == null) {
            usage("No value after -records");
          }
          try {
            records=Long.parseLong(val);
          }
 catch (          NumberFormatException e) {
            usage(val + " is not a number");
          }
          if (records <= 0) {
            usage(val + " is not a positive integer");
          }
        }
 else         if (name.equals("-key")) {
          if (val == null) {
            usage("No value after -key");
          }
          try {
            keySize=Integer.parseInt(val);
          }
 catch (          NumberFormatException e) {
            usage(val + " is not a number");
          }
          if (keySize <= 0) {
            usage(val + " is not a positive integer");
          }
        }
 else         if (name.equals("-data")) {
          if (val == null) {
            usage("No value after -data");
          }
          try {
            dataSize=Integer.parseInt(val);
          }
 catch (          NumberFormatException e) {
            usage(val + " is not a number");
          }
          if (dataSize <= 0) {
            usage(val + " is not a positive integer");
          }
        }
 else         if (name.equals("-nodemax")) {
          if (val == null) {
            usage("No value after -nodemax");
          }
          try {
            nodeMax=Integer.parseInt(val);
          }
 catch (          NumberFormatException e) {
            usage(val + " is not a number");
          }
          if (nodeMax <= 0) {
            usage(val + " is not a positive integer");
          }
        }
 else         if (name.equals("-density")) {
          if (val == null) {
            usage("No value after -density");
          }
          try {
            density=Integer.parseInt(val);
          }
 catch (          NumberFormatException e) {
            usage(val + " is not a number");
          }
          if (density < 1 || density > 100) {
            usage(val + " is not betwen 1 and 100");
          }
        }
 else         if (name.equals("-overhead")) {
          if (val == null) {
            usage("No value after -overhead");
          }
          try {
            overhead=Long.parseLong(val);
          }
 catch (          NumberFormatException e) {
            usage(val + " is not a number");
          }
          if (overhead < 0) {
            usage(val + " is not a non-negative integer");
          }
        }
 else         if (name.equals("-measure")) {
          if (val == null) {
            usage("No value after -measure");
          }
          measureDir=new File(val);
        }
 else         if (name.equals("-measurerandom")) {
          measureRandom=true;
        }
 else {
          usage("Unknown arg: " + name);
        }
      }
      if (records == 0) {
        usage("-records not specified");
      }
      if (keySize == 0) {
        usage("-key not specified");
      }
      printCacheSizes(System.out,records,keySize,dataSize,nodeMax,density,overhead);
      if (measureDir != null) {
        measure(System.out,measureDir,records,keySize,dataSize,nodeMax,measureRandom);
      }
    }
 catch (    Throwable e) {
      e.printStackTrace(System.out);
    }
  }
  private static void usage(  String msg){
    if (msg != null) {
      System.out.println(msg);
    }
    System.out.println("usage:" + "\njava " + CmdUtil.getJavaCommand(DbCacheSize.class) + "\n   -records <count>"+ "\n      # Total records (key/data pairs); required"+ "\n   -key <bytes> "+ "\n      # Average key bytes per record; required"+ "\n  [-data <bytes>]"+ "\n      # Average data bytes per record; if omitted no leaf"+ "\n      # node sizes are included in the output"+ "\n  [-nodemax <entries>]"+ "\n      # Number of entries per Btree node; default: 128"+ "\n  [-density <percentage>]"+ "\n      # Percentage of node entries occupied; default: 80"+ "\n  [-overhead <bytes>]"+ "\n      # Overhead of non-Btree objects (log buffers, locks,"+ "\n      # etc); default: 10% of total cache size"+ "\n  [-measure <environmentHomeDirectory>]"+ "\n      # An empty directory used to write a database to find"+ "\n      # the actual cache size; default: do not measure"+ "\n  [-measurerandom"+ "\n      # With -measure insert randomly generated keys;"+ "\n      # default: insert sequential keys");
    System.exit(2);
  }
  private static void printCacheSizes(  PrintStream out,  long records,  int keySize,  int dataSize,  int nodeMax,  int density,  long overhead){
    out.println("Inputs:" + " records=" + records + " keySize="+ keySize+ " dataSize="+ dataSize+ " nodeMax="+ nodeMax+ " density="+ density+ '%'+ " overhead="+ ((overhead > 0) ? overhead : 10)+ "%");
    int nodeAvg=(nodeMax * density) / 100;
    long nBinEntries=(records * nodeMax) / nodeAvg;
    long nBinNodes=(nBinEntries + nodeMax - 1) / nodeMax;
    long nInNodes=0;
    int nLevels=1;
    for (long n=nBinNodes; n > 0; n/=nodeMax) {
      nInNodes+=n;
      nLevels+=1;
    }
    long minInSize=nInNodes * calcInSize(nodeMax,nodeAvg,keySize,true);
    long maxInSize=nInNodes * calcInSize(nodeMax,nodeAvg,keySize,false);
    long lnSize=0;
    if (dataSize > 0) {
      lnSize=records * calcLnSize(dataSize);
    }
    out.println();
    out.println(HEADER);
    out.println(line(minInSize,overhead,"Minimum, internal nodes only"));
    out.println(line(maxInSize,overhead,"Maximum, internal nodes only"));
    if (dataSize > 0) {
      out.println(line(minInSize + lnSize,overhead,"Minimum, internal nodes and leaf nodes"));
      out.println(line(maxInSize + lnSize,overhead,"Maximum, internal nodes and leaf nodes"));
    }
 else {
      out.println("\nTo get leaf node sizing specify -data");
    }
    out.println("\nBtree levels: " + nLevels);
  }
  private static int calcInSize(  int nodeMax,  int nodeAvg,  int keySize,  boolean lsnCompression){
    int size=MemoryBudget.IN_FIXED_OVERHEAD;
    size+=MemoryBudget.byteArraySize(nodeMax) + (nodeMax * (2 * MemoryBudget.ARRAY_ITEM_OVERHEAD));
    if (lsnCompression) {
      size+=MemoryBudget.byteArraySize(nodeMax * 2);
    }
 else {
      size+=MemoryBudget.BYTE_ARRAY_OVERHEAD + (nodeMax * MemoryBudget.LONG_OVERHEAD);
    }
    size+=(nodeAvg + 1) * MemoryBudget.byteArraySize(keySize);
    return size;
  }
  private static int calcLnSize(  int dataSize){
    return MemoryBudget.LN_OVERHEAD + MemoryBudget.byteArraySize(dataSize);
  }
  private static String line(  long btreeSize,  long overhead,  String comment){
    long cacheSize;
    if (overhead == 0) {
      cacheSize=(100 * btreeSize) / 90;
    }
 else {
      cacheSize=btreeSize + overhead;
    }
    StringBuffer buf=new StringBuffer(100);
    column(buf,INT_FORMAT.format(cacheSize));
    column(buf,INT_FORMAT.format(btreeSize));
    column(buf,comment);
    return buf.toString();
  }
  private static void column(  StringBuffer buf,  String str){
    int start=buf.length();
    while (buf.length() - start + str.length() < COLUMN_WIDTH) {
      buf.append(' ');
    }
    buf.append(str);
    for (int i=0; i < COLUMN_SEPARATOR; i+=1) {
      buf.append(' ');
    }
  }
  private static void measure(  PrintStream out,  File dir,  long records,  int keySize,  int dataSize,  int nodeMax,  boolean randomKeys) throws DatabaseException {
    String[] fileNames=dir.list();
    if (fileNames != null && fileNames.length > 0) {
      usage("Directory is not empty: " + dir);
    }
    Environment env=openEnvironment(dir,true);
    Database db=openDatabase(env,nodeMax,true);
    try {
      out.println("\nMeasuring with cache size: " + INT_FORMAT.format(env.getConfig().getCacheSize()));
      insertRecords(out,env,db,records,keySize,dataSize,randomKeys);
      hook832(out,env);
      db.close();
      env.close();
      env=openEnvironment(dir,false);
      db=openDatabase(env,nodeMax,false);
      out.println("\nPreloading with cache size: " + INT_FORMAT.format(env.getConfig().getCacheSize()));
      preloadRecords(out,db);
      hook831(out,env);
    }
  finally {
      try {
        db.close();
        env.close();
      }
 catch (      Exception e) {
        out.println("During close: " + e);
      }
    }
  }
  private static Environment openEnvironment(  File dir,  boolean allowCreate) throws DatabaseException {
    EnvironmentConfig envConfig=new EnvironmentConfig();
    envConfig.setAllowCreate(allowCreate);
    envConfig.setCachePercent(90);
    return new Environment(dir,envConfig);
  }
  private static Database openDatabase(  Environment env,  int nodeMax,  boolean allowCreate) throws DatabaseException {
    DatabaseConfig dbConfig=new DatabaseConfig();
    dbConfig.setAllowCreate(allowCreate);
    dbConfig.setNodeMaxEntries(nodeMax);
    return env.openDatabase(null,"foo",dbConfig);
  }
  private static void insertRecords(  PrintStream out,  Environment env,  Database db,  long records,  int keySize,  int dataSize,  boolean randomKeys) throws DatabaseException {
    new DbCacheSize_insertRecords(out,env,db,records,keySize,dataSize,randomKeys).execute();
  }
  private static void preloadRecords(  final PrintStream out,  final Database db) throws DatabaseException {
    Thread thread=new Thread(){
      public void run(){
        while (true) {
          try {
            out.print(".");
            out.flush();
            Thread.sleep(5 * 1000);
          }
 catch (          InterruptedException e) {
            break;
          }
        }
      }
    }
;
    thread.start();
    db.preload(0);
    thread.interrupt();
    try {
      thread.join();
    }
 catch (    InterruptedException e) {
      e.printStackTrace(out);
    }
  }
@MethodObject static class DbCacheSize_insertRecords {
    DbCacheSize_insertRecords(    PrintStream out,    Environment env,    Database db,    long records,    int keySize,    int dataSize,    boolean randomKeys){
      this.out=out;
      this.env=env;
      this.db=db;
      this.records=records;
      this.keySize=keySize;
      this.dataSize=dataSize;
      this.randomKeys=randomKeys;
    }
    void execute() throws DatabaseException {
      try {
        key=new DatabaseEntry();
        data=new DatabaseEntry(new byte[dataSize]);
        bigInt=BigInteger.ZERO;
        rnd=new Random(123);
        for (int i=0; i < records; i+=1) {
          if (randomKeys) {
            a=new byte[keySize];
            rnd.nextBytes(a);
            key.setData(a);
          }
 else {
            bigInt=bigInt.add(BigInteger.ONE);
            a2=bigInt.toByteArray();
            if (a2.length < keySize) {
              a3=new byte[keySize];
              System.arraycopy(a2,0,a3,a3.length - a2.length,a2.length);
              a2=a3;
            }
 else             if (a2.length > keySize) {
              out.println("*** Key doesn't fit value=" + bigInt + " byte length="+ a2.length);
              return;
            }
            key.setData(a2);
          }
          status=db.putNoOverwrite(null,key,data);
          if (status == OperationStatus.KEYEXIST && randomKeys) {
            i-=1;
            out.println("Random key already exists -- retrying");
            continue;
          }
          if (status != OperationStatus.SUCCESS) {
            out.println("*** " + status);
            return;
          }
          if (i % 10000 == 0) {
            this.hook833();
            out.print(".");
            out.flush();
          }
        }
      }
 catch (      ReturnVoid r) {
        return;
      }
    }
    protected PrintStream out;
    protected Environment env;
    protected Database db;
    protected long records;
    protected int keySize;
    protected int dataSize;
    protected boolean randomKeys;
    protected DatabaseEntry key;
    protected DatabaseEntry data;
    protected BigInteger bigInt;
    protected Random rnd;
    protected byte[] a;
    protected byte[] a2;
    protected byte[] a3;
    protected OperationStatus status;
    protected EnvironmentStats stats;
    protected void hook833() throws DatabaseException {
    }
  }
  protected static void hook831(  PrintStream out,  Environment env) throws DatabaseException {
  }
  protected static void hook832(  PrintStream out,  Environment env) throws DatabaseException {
  }
}
