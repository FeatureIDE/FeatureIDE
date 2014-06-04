public class LogEntry {
	//@ private invariant source != null;
private Account source;

	//@ private invariant destination != null;
private Account destination;

	private int value;

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.logging;
	 @ requires FM.FeatureModel.logging ==> (source != null);
	 @ requires FM.FeatureModel.logging ==> (destination != null);
	 @ requires FM.FeatureModel.logging ==> (source != destination);
	 @*/
	public LogEntry(Account source,Account destination,int amount){
		if (FM.FeatureModel.logging) {
			this.source = source;
			this.destination = destination;
			this.value = amount;
				}
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.logging;
	 @ ensures FM.FeatureModel.logging ==> (\result != null);
	 @*/
	public  /*@pure@*/  Account getSource(){
		return source;
	}

	/*@ 
	 
	 @ requires FM.FeatureModel.valid();
	 @ requires FM.FeatureModel.logging;
	 @ ensures FM.FeatureModel.logging ==> (\result != null);
	 @*/
	public  /*@pure@*/  Account getDestination(){
		return destination;
	}

	/*@  @*/
	public  /*@pure@*/  int getAmount(){
		return value;
	}


}
