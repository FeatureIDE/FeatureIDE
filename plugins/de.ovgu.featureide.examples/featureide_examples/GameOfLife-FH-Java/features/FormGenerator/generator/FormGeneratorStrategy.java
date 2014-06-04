package generator;

public class FormGeneratorStrategy implements GeneratorStrategy {
	
	private final int xSize;
	private final int ySize;

	public FormGeneratorStrategy(int xSize, int ySize) {
		this.xSize = xSize;
		this.ySize = ySize;
	}
	public String toString() {
		return "Form Generator";
	}
	
    public int getNext(int x, int y) {
        if(x == 0 || x == xSize || y == 0 || y == ySize) {
        	return 0;
        } else {
        	if( x == y || x+1 == y || y+1 == x ) {
        		return 1;
        	} else {
        		return 0;
        	}
        }
    }
}