package generator;

public class ClearGeneratorStrategy implements GeneratorStrategy {
	
	public String toString() {
		return "Clear Generator";
	}
	
    public int getNext(int x, int y) {
        return 0;
    }
}