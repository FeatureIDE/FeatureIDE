

public class CountUnead {

	public CountUnead(int i) {
		double of = Math.pow(2, Math.pow(2, i));
		double x = of;
		for (int k = 1;k < i+1;k++) {
			of = of -  Math.pow(0.25, k)*x;
		}
		of -= 1;
		
		double of2 = Math.pow(2, Math.pow(2, i));
		for (int k = 0;k < i;k++) {
			of2 -= Math.pow(2, Math.pow(2, k));
		}
		
		newMethod(i);
		
		
//		ArrayList<ArrayList<ArrayList<Boolean>>> array= new ArrayList<ArrayList<ArrayList<Boolean>>>(); 
//		init (array, i);
//		fill(array);
//		count(array, i);
		System.out.println("Count Features: " + i + " Count Models: " +  (Math.pow(2, Math.pow(2, i)) - deadModels) + " of:" + of + " of2:" + of2);
	}
	int deadModels = 0;
	private void newMethod(int i) {
		int pointer;
		double x2;
		
		boolean dead;
		int counter;
		int c;
		boolean set;
		double pow2 = Math.pow(2, i);
		boolean[] array = new boolean[(int) pow2];
		double pow = Math.pow(2, pow2);
		for (double x = 0;x < pow; x++) {
			if (x%10000000 == 0) {
				System.out.println(pow - x);
			}
			pointer = 0;
			x2 = x;
			for (double j = pow/2; j >= 0; j=j/2) {
				if (j <= x2) {
					array[pointer] = true;
					x2 -= j;
				}
				if (x2 == 0) {
					break;
				}
				pointer++;
			}

			dead = true;
			counter = 1;
			c = 1;
			set = false;
			for (int k = 0; k < i;k++) {
				dead = true;
				for (int m = 0; m < array.length;m++) {
					if (set) {
						if (array[m]) {
							dead = false;
							break;
						}
					}
					counter--;
					if (counter == 0) {
						counter = c;
						set = !set;
					}
				}
				if (dead) {
					break;
				}
				c = c*2;
				counter = c;
				
			}
			if (dead) {
				deadModels++;
			}
			array = new boolean[(int) pow2];
			
		}
		System.out.println(deadModels);
	}

	

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		for (int i = 1; i < 6; i++) {
			new CountUnead(i);
		}
	}


}
