public aspect Wonderful {

	after(): call(void Main.print()) {
		System.out.print(" wonderful");
	}

}