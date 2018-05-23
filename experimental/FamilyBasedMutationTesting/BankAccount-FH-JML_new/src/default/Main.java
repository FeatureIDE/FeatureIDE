public  class Main {
	/*@  @*/
	public static void main(String[] args) {
		if (FM.FeatureModel.valid()) {
			new Main();
		}
	}

	private Object a;

	private Object b;

	/*@  @*/
	public Main  () {
		if (FM.FeatureModel.bankaccount) {
			a = new Application();
			b = new Application();
			getA().account.update(100);
			getB().account.update(200);
			getA().nextDay();
			getB().nextYear();
				}
	
		if (FM.FeatureModel.creditworthiness) {
			getA().account.credit(10);
			getB().account.credit(20);
				}
	
		if (FM.FeatureModel.transaction) {
			new Transaction().transfer(getA().account, getB().account, 30);
			new Transaction().transfer(getB().account, getA().account, 100);
				}
	}

	/*@  @*/
	private Application getA() {
		return (Application)a;
	}

	/*@  @*/
	private Application getB() {
		return (Application)b;
	}


}
