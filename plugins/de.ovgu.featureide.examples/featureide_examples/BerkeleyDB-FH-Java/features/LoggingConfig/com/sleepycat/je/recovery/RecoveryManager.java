package com.sleepycat.je.recovery;
public class RecoveryManager {
  protected void hook558() throws DatabaseException, IOException {
    Tracer.trace(Level.CONFIG,env,"Recovery checkpoint search, " + info);
    original();
  }
  protected void hook559() throws DatabaseException, IOException {
    Tracer.trace(Level.CONFIG,env,"Recovery underway, found end of log");
    original();
  }
  protected void hook560() throws DatabaseException, IOException {
    Tracer.trace(Level.CONFIG,env,"Recovery w/no files.");
    original();
  }
  protected void hook561(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(10,start,end) + info.toString());
    original(start,end);
  }
  protected void hook562(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(9,start,end) + info.toString());
    Tracer.trace(Level.CONFIG,env,passStartHeader(10) + "redo LNs");
    original(start,end);
  }
  protected void hook563() throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passStartHeader(9) + "undo LNs");
    original();
  }
  protected void hook564(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(8,start,end) + info.toString());
    original(start,end);
  }
  protected void hook565(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(7,start,end) + info.toString());
    Tracer.trace(Level.CONFIG,env,passStartHeader(8) + "read dup BINDeltas");
    original(start,end);
  }
  protected void hook566(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(6,start,end) + info.toString());
    Tracer.trace(Level.CONFIG,env,passStartHeader(7) + "read dup INs");
    original(start,end);
  }
  protected void hook567(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(5,start,end) + info.toString());
    Tracer.trace(Level.CONFIG,env,passStartHeader(6) + "read BINDeltas");
    original(start,end);
  }
  protected void hook568(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(4,start,end) + info.toString());
    Tracer.trace(Level.CONFIG,env,passStartHeader(5) + "read other INs");
    original(start,end);
  }
  protected void hook569(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(3,start,end) + info.toString());
    Tracer.trace(Level.CONFIG,env,passStartHeader(4) + "redo map LNs");
    original(start,end);
  }
  protected void hook570(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(2,start,end) + info.toString());
    Tracer.trace(Level.CONFIG,env,passStartHeader(3) + "undo map LNs");
    original(start,end);
  }
  protected void hook571(  long start,  long end) throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passEndHeader(1,start,end) + info.toString());
    Tracer.trace(Level.CONFIG,env,passStartHeader(2) + "read map BINDeltas");
    original(start,end);
  }
  protected void hook572() throws IOException, DatabaseException {
    Tracer.trace(Level.CONFIG,env,passStartHeader(1) + "read map INs");
    original();
  }
}
