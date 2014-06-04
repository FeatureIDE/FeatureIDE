package com.sleepycat.je.log;
import java.util.logging.Handler;
import java.util.logging.LogRecord;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
/** 
 * Handler for java.util.logging. Takes logging records and publishes them into
 * the database log.
 */
public class TraceLogHandler extends Handler {
  private EnvironmentImpl env;
  public TraceLogHandler(  EnvironmentImpl env){
    this.env=env;
  }
  public void close(){
  }
  public void flush(){
  }
  public void publish(  LogRecord l){
    if (!env.isReadOnly() && !env.mayNotWrite()) {
      try {
        Tracer newRec=new Tracer(l.getMessage());
        env.getLogManager().log(newRec);
      }
 catch (      DatabaseException e) {
        System.err.println("Problem seen while tracing into " + "the database log:");
        e.printStackTrace();
      }
    }
  }
}
