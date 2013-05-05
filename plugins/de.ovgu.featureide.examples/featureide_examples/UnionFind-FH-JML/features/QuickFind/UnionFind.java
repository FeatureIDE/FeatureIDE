
public class UnionFind {
	

	

	

	    // are elements p and q in the same component?
		/*@
		 	ensures \original_clause;
		 	ensures \result == (id[p] == id[q]);
		 @*/
	    public /*@pure@*/ boolean connected(int p, int q) {
	        return id[p] == id[q];
	    }

	   
	    /*@
	       \original_spec
	           
	     */
	    public void union(int p, int q) {
	        if (connected(p, q)) return;
	        int pid = id[p];
	        for (int i = 0; i < id.length; i++)
	            if (id[i] == pid) id[i] = id[q]; 
	        count--;
	    }



	
}
