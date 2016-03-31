
public class World implements interfaces.Print, interfaces.Announce{

	@Override
	public void announce() {
		System.err.print("World");
	}

	@Override
	public void print() {
		System.out.print("World");
	}
}
