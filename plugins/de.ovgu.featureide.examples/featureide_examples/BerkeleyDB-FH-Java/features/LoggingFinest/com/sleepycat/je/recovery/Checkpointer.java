package com.sleepycat.je.recovery;
public class Checkpointer {
@MethodObject static class Checkpointer_isRunnable {
    protected void hook517() throws DatabaseException {
    }
    protected void hook518() throws DatabaseException {
    }
    protected void hook521() throws DatabaseException {
      sb=new StringBuffer();
{
        this.hook517();
      }
      if (nextLsn != DbLsn.NULL_LSN) {
        sb.append(" " + "nextLsn=").append(DbLsn.getNoFormatString(nextLsn));
      }
      if (_this.lastCheckpointEnd != DbLsn.NULL_LSN) {
        sb.append(" lastCkpt=");
        sb.append(DbLsn.getNoFormatString(_this.lastCheckpointEnd));
      }
{
        this.hook518();
      }
      sb.append(" force=").append(config.getForce());
      Tracer.trace(Level.FINEST,_this.envImpl,sb.toString());
      original();
    }
  }
}
