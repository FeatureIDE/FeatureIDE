
public class IntList {
    /*@ invariant this != null;@*/ 
	/*@ invariant data != null;@*/
    public int[] data;
    
    public IntList() {
        data = new int[0];
    }
    
    /*@
    @ assignable data;
    @ ensures (\exists int z; 0 <= z && z < data.length && data[z] == newTop)
    @ && (\forall int k; 0 <= k && k < \old(data).length 
    @    ==> (\exists int z; 0 <= z && z < data.length && data[z] == \old(data[k])));
    @*/
    public void push(int newTop) {
        int[] tmp = new int[data.length+1];
        tmp[tmp.length-1] = newTop;
        for(int i = 0; i < data.length; i++) {
            tmp[i] = data[i];
        }
        //@ assert (tmp[tmp.length-1] == newTop);
        data = tmp;
    }
    
    public void printContents() {
    	System.out.print("List contents:");
    	for (int i = 0; i < data.length; i++) {
    		System.out.print(" " + data[i]);
    	}
    	System.out.println();
    }
    
}
