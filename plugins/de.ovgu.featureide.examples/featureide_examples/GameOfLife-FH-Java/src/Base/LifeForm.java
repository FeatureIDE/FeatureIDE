


 


class  LifeForm {
	
		private final int type;

	
		private final int[] neighbourhood;

	
		private final int x;

	
		private final int y;

	
		
		public LifeForm(int x, int y, int type, int[] neighbourhood) {
			this.x = x;
			this.y = y;
			this.type = type;
			this.neighbourhood = neighbourhood;
		}

	
		
		public int getType() {
			return type;
		}

	
		
		public int[] getNeighbourhood() {
			return neighbourhood;
		}

	
		
		public int getX() {
			return x;
		}

	
		
		public int getY() {
			return y;
		}


}
