
public class UnionFind {


	 

	    // Return component identifier for component containing p
	    public int find(int p) {
	        int root = p;
	        while (root != id[root])
	            root = id[root];
	        while (p != root) {
	            int newp = id[p];
	            id[p] = root;
	            p = newp;
	        }
	        return root;
	    }


	  



	}

