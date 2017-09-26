public class LogFile {
    
    /*@ public invariant
      @    logArray.length == logFileSize && 
      @    currentRecord < logFileSize && 
      @    currentRecord >= 0 && \nonnullelements(logArray);
      @*/
    private /*@ spec_public @*/ static int logFileSize = 3;
    private /*@ spec_public @*/ int currentRecord;
    private /*@ spec_public @*/ LogRecord[] logArray = new LogRecord[logFileSize];
    
    public /*@pure@*/ LogFile() {
	int i=0;
	while(i<logArray.length){
	    logArray[i++] = new LogRecord();
	}
	currentRecord = 0;
    }
    
    
    /*@ public normal_behavior
      @    requires balance >= 0;
      @    ensures \old(currentRecord) + 1 != logFileSize ? 
      @        currentRecord == \old(currentRecord) + 1 : currentRecord == 0;
      @    ensures logArray[currentRecord].balance == balance;
      @    assignable currentRecord, logArray[*];
      @*/
    public void addRecord(int balance) throws CardException {
	currentRecord++;
	if (currentRecord == logFileSize) currentRecord = 0;
	logArray[currentRecord].setRecord(balance);
    }
    
}
