

class Playground implements Cloneable{
	public Playground clone() {
		Playground clone = new Playground(xSize, ySize, generation);
		int[][] newField = new int[xSize][ySize];
		for(int i = 0; i < xSize; i++) {
			for (int j = 0; j < ySize; j++) {
				newField[i][j] = field[i][j];
			}
		}
		clone.field = newField;
		return clone;
	}
}