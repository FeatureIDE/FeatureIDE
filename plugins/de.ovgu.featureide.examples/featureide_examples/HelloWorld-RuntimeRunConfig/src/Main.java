import java.io.IOException;
import java.util.Arrays;
import java.util.List;

public class Main {
	public static void main(String[] args) throws IOException {

		List<String> list = Arrays.asList(args);

		if (list.contains("Hello")) {
			System.out.print("Hello");
		}

		if (list.contains("Beautiful")) {
			System.out.print(" beautiful");
		}

		if (list.contains("Wonderful")) {
			System.out.print(" wonderful");
		}

		if (list.contains("World")) {
			System.out.println(" World!");
		}

	}
}
