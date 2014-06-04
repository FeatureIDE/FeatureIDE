

class Playground {

	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Gen: " + generation);
		sb.append("\n");
		for(int i = 0; i < xSize; i++) {
			for (int j = 0; j < ySize; j++) {
				sb.append(field[i][j] + " ");
			}
			sb.append("\n");
		}
		return sb.toString();
	}
	
	public boolean equals(Object o) {
		if(o == null) {
			return false;
		} else if (o instanceof Playground) {
			Playground op = (Playground) o;
			return op.generation == this.generation && op.xSize == this.xSize &&
				   op.ySize == this.ySize && Arrays.deepEquals(op.field, this.field);
		} else {
			return false;
		}
	}
}