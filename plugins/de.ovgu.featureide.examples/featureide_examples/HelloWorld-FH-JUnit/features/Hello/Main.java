public class Main {

	protected StringBuilder buildWorld(StringBuilder builder){
		return builder.append("Hello");
	}
	
	public static void main(String[] args){
		StringBuilder builder = new Main().buildWorld(new StringBuilder());
		System.out.println(builder);
	}
}
