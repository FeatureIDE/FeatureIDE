public aspect Hello {

	before(): call(void Main.print()) {
		System.out.print("Hello");
	}

}