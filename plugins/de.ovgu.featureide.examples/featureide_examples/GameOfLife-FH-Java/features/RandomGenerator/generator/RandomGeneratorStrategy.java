package generator;

public class RandomGeneratorStrategy implements GeneratorStrategy {

    public int getNext(int x, int y) {
        return (int) Math.round(Math.random());
    }
    public String toString() {
		return "Random Generator";
	}

}