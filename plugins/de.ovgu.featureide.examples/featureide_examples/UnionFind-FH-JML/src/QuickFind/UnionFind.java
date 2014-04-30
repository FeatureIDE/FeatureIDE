public  class UnionFind {
	 /*@spec_public@*/   private int[] id;

	 /*@spec_public@*/   private int count;

	/*@ 
	 requires N > 0;
       ensures count == N; 
	   ensures (\forall int i; 0 <= i && i < N;
id[i] == i); @*/
	public UnionFind(int N) {
        count = N;
        id = new int[N];
        for (int i = 0; i < N; i++)
        id[i] = i;
    }

	/*@ 
	 ensures \result == count; @*/
	public int count() {
        return count;
    }

	/*@ 
	 ensures true;
		 	ensures \result == (id[p] == id[q]); @*/
	public /*@pure@*/ boolean connected  (int p, int q) {
	        return id[p] == id[q];
	    }

	/*@ 
	 true_spec; @*/
	public void union  (int p, int q) {
	        if (connected(p, q)) return;
	        int pid = id[p];
	        for (int i = 0; i < id.length; i++)
	            if (id[i] == pid) id[i] = id[q]; 
	        count--;
	    }


	public static void main(String[] args) {
	     	
	    	In in = new In("TestData/mediumUF.txt");
	        int N = in.readInt();
	        Stopwatch s = new Stopwatch();
	        UnionFind uf = new UnionFind(N);
	        
	        
	         
	        
	        while (!in.isEmpty()) {
	            int p = in.readInt();
	            int q = in.readInt();
	            if (uf.connected(p, q)) continue;
	            uf.union(p, q);
	            
	        }
	        StdOut.println(s.elapsedTime() + " time");
	        uf.count();
	        StdOut.println(uf.count() + " components");
	   
	    }


}
