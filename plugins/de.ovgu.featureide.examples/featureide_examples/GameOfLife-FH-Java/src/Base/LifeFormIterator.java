


import java.util.Iterator; 

 

class  LifeFormIterator  implements Iterator {
	

	/**
	 * 
	 */
	private final Playground playground;

	

	/**
	 * @param playground
	 */
	LifeFormIterator(Playground playground) {
		this.playground = playground;
	}

	

	private int currentX = 0;

	
	private int currentY = 0;

	
	
	public boolean hasNext() {
		return (currentX < this.playground.xSize) && (currentY < this.playground.ySize);
	}

	

	
	public LifeForm next() {
		LifeForm result = new LifeForm(currentX, currentY, this.playground.field[currentX][currentY], this.playground.getNeighbourhood(currentX, currentY));
		currentX++;
		if(currentX >= this.playground.xSize) {
			currentX = 0;
			currentY++;
			assert (currentY < this.playground.ySize);
		}
		return result;
	}

	

	public void remove() {
		throw new UnsupportedOperationException();
	}


}
