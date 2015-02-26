public   class  Main {
	

	 private void  print__wrappee__Hello  () {
		System.out.print("Hello");
	}

	
	
	 private void  print__wrappee__Beautiful  (){
		print__wrappee__Hello();
		System.out.print(" beautiful");
	}

	
	
	protected void print() {
		print__wrappee__Beautiful();
		System.out.print(" World!");
	}

	
	
	public static void main(String[] args){
		new Main().print();
	}


}
