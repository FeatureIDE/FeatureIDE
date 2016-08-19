public class Main {

	protected StringBuilder buildWorld(StringBuilder builder) {

		// #if Hello
		builder.append("Hello");
		// #endif
		// #if Beautiful
//@		builder.append(" beautiful");
		// #endif
		// #if Wonderful
		 builder.append(" wonderful");
		// #endif
		// #if World
		builder.append(" world");
		// #endif

		return builder;
	}

	public static void main(String[] args) {

		StringBuilder builder = new Main().buildWorld(new StringBuilder());
		System.out.println(builder);
	}
}
