package com.sleepycat.je.cleaner;
public class UtilizationProfile {
@MethodObject static class UtilizationProfile_populateCache {
    protected void hook194() throws DatabaseException {
      oldMemorySize=_this.fileSummaryMap.size() * MemoryBudget.UTILIZATION_PROFILE_ENTRY;
      original();
    }
    protected void hook195() throws DatabaseException {
      newMemorySize=_this.fileSummaryMap.size() * MemoryBudget.UTILIZATION_PROFILE_ENTRY;
      mb=_this.env.getMemoryBudget();
      mb.updateMiscMemoryUsage(newMemorySize - oldMemorySize);
      original();
    }
  }
@MethodObject static class UtilizationProfile_removeFile {
    protected void hook192() throws DatabaseException {
      mb=_this.env.getMemoryBudget();
      mb.updateMiscMemoryUsage(0 - MemoryBudget.UTILIZATION_PROFILE_ENTRY);
      original();
    }
  }
@MethodObject static class UtilizationProfile_putFileSummary {
    protected void hook193() throws DatabaseException {
      mb=_this.env.getMemoryBudget();
      mb.updateMiscMemoryUsage(MemoryBudget.UTILIZATION_PROFILE_ENTRY);
      original();
    }
  }
@MethodObject static class UtilizationProfile_clearCache {
    void execute(){
      memorySize=_this.fileSummaryMap.size() * MemoryBudget.UTILIZATION_PROFILE_ENTRY;
      mb=_this.env.getMemoryBudget();
      mb.updateMiscMemoryUsage(0 - memorySize);
      original();
    }
  }
}
