public aspect World {

	after(): execution(void Main.print()) {
		System.out.print(" world!");
	}

}