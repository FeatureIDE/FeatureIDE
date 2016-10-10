public aspect World {

	declare precedence: World, Wonderful, Beautiful, Hello; 

	after(): call(void Main.print()) {
		System.out.print(" world!");
	}

}