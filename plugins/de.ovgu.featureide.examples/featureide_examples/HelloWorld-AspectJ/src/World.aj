public aspect World {

	after(): call(void Main.print()) {
		System.out.print(" world!");
	}

}