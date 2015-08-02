public   class  Main {
	
	
	 private StringBuilder  buildWorld__wrappee__Wonderful  (StringBuilder builder){
		return builder.append(" wonderful");
	}

	
	
	protected StringBuilder buildWorld(StringBuilder builder){
		return buildWorld__wrappee__Wonderful(builder).append(" World!");
	}

	
	
	public static void main(String[] args){
		StringBuilder builder = new Main().buildWorld(new StringBuilder());
		System.out.println(builder);
	}


}
