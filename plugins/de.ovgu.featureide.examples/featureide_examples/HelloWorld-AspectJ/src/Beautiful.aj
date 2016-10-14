public aspect Beautiful {

	after(): call(void Main.print()) {
		System.out.print(" beautiful");
	}

}