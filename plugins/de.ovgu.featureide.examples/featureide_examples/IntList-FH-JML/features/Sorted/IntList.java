
public class IntList {

	/*@ invariant (\forall int k; 0 <= k && k < data.length-1; data[k] >= data[k+1]);@*/
	
	public void push(int newTop) {
		original(newTop);
		sort();
	}
	
	/*@ assignable data[0..data.length-1];
	  @ ensures (\forall int k; 0 <= k && k < data.length-1; data[k] >= data[k+1]);
	  @*/
	private /*@ helper */ void sort() {
		for (int i = 0; i < data.length; i++) {
			//@ assert (\forall int k; 0 <= k && k < i;
			//@        (\forall int m; k < m && m < data.length; data[k] >= data[m]));
			 
			for (int j = data.length-2; j >= 0; j--) {
				if (data[j] < data[j+1]) {
					int tmp = data[j];
					data[j] = data[j+1];
					data[j+1] = tmp;
				}
				//@ assert data[j] >= data[j+1];
			}
		}
	}
    
}
