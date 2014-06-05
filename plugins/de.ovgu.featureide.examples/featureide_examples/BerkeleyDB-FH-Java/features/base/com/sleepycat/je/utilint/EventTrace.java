package com.sleepycat.je.utilint;
import de.ovgu.cide.jakutil.*;
/** 
 * Internal class used for transient event tracing.  Subclass this with
 * specific events.  Subclasses should have toString methods for display and
 * events should be added by calling EventTrace.addEvent();
 */
public class EventTrace {
  static private int MAX_EVENTS=100;
  static public final boolean TRACE_EVENTS=false;
  static int currentEvent=0;
  static final EventTrace[] events=new EventTrace[MAX_EVENTS];
  static final int[] threadIdHashes=new int[MAX_EVENTS];
  static boolean disableEvents=false;
  protected String comment;
  public EventTrace(  String comment){
    this.comment=comment;
  }
  public EventTrace(){
    comment=null;
  }
  public String toString(){
    return comment;
  }
  static public void addEvent(  EventTrace event){
    if (disableEvents) {
      return;
    }
    int nextEventIdx=currentEvent++ % MAX_EVENTS;
    events[nextEventIdx]=event;
    threadIdHashes[nextEventIdx]=System.identityHashCode(Thread.currentThread());
  }
  static public void addEvent(  String comment){
    if (disableEvents) {
      return;
    }
    addEvent(new EventTrace(comment));
  }
  static public void dumpEvents(){
    if (disableEvents) {
      return;
    }
    System.out.println("----- Event Dump -----");
    EventTrace[] oldEvents=events;
    int[] oldThreadIdHashes=threadIdHashes;
    disableEvents=true;
    int j=0;
    for (int i=currentEvent; j < MAX_EVENTS; i++) {
      EventTrace ev=oldEvents[i % MAX_EVENTS];
      if (ev != null) {
        int thisEventIdx=i % MAX_EVENTS;
        System.out.print(oldThreadIdHashes[thisEventIdx] + " ");
        System.out.println(j + "(" + thisEventIdx+ "): "+ ev);
      }
      j++;
    }
  }
static public class ExceptionEventTrace extends EventTrace {
    private Exception event;
    public ExceptionEventTrace(){
      event=new Exception();
    }
    public String toString(){
      return Tracer.getStackTrace(event);
    }
  }
}
