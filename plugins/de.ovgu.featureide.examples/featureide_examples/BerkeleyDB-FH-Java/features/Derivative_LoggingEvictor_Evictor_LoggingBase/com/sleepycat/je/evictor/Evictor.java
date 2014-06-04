package com.sleepycat.je.evictor;
public class Evictor {
@MethodObject static class Evictor_evictBatch {
    protected void hook368() throws DatabaseException {
    }
    protected void hook369() throws DatabaseException {
    }
    protected void hook371() throws DatabaseException {
      logger=_this.envImpl.getLogger();
      if (logger.isLoggable(_this.detailedTraceLevel)) {
        msg="Evictor: ";
        this.hook369();
        msg+=" finished=" + finished + " source="+ source+ " requiredEvictBytes="+ _this.formatter.format(requiredEvictBytes)+ " evictBytes="+ _this.formatter.format(evictBytes)+ " inListSize="+ inListStartSize+ " nNodesScanned="+ _this.nNodesScannedThisRun;
        this.hook368();
        msg+=" nBatchSets=" + nBatchSets;
        Tracer.trace(_this.detailedTraceLevel,_this.envImpl,msg);
      }
      original();
    }
  }
@MethodObject static class Evictor_isRunnable {
    protected void hook370() throws DatabaseException {
    }
    protected void hook372() throws DatabaseException {
      logger=_this.envImpl.getLogger();
      if (logger.isLoggable(_this.detailedTraceLevel)) {
        r=Runtime.getRuntime();
        totalBytes=r.totalMemory();
        freeBytes=r.freeMemory();
        usedBytes=r.totalMemory() - r.freeMemory();
        sb=new StringBuffer();
        sb.append(" source=").append(source);
        this.hook370();
        sb.append(" requiredEvict=").append(_this.formatter.format(_this.currentRequiredEvictBytes));
        sb.append(" JVMtotalBytes= ").append(_this.formatter.format(totalBytes));
        sb.append(" JVMfreeBytes= ").append(_this.formatter.format(freeBytes));
        sb.append(" JVMusedBytes= ").append(_this.formatter.format(usedBytes));
        logger.log(_this.detailedTraceLevel,sb.toString());
      }
      original();
    }
  }
}
