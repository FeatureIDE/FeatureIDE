public aspect Hello {
	
	after(): call(void Main.print()) {
		System.out.print("Hello");
	}

}