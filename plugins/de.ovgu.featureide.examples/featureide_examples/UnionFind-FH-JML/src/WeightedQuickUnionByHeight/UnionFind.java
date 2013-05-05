public   class  UnionFind {
	
 /*@spec_public@*/   private  int[] id;

	    
 /*@spec_public@*/   private  int count;

	/*@    
    
    
    
       requires N > 0;
       ensures count == N; 
	   ensures (\forall int i; 0 <= i && i < N;
id[i] == i);
	@*/    

    
    public UnionFind  (int N) {
        count = N;
        id = new int[N];
        for (int i = 0; i < N; i++)
        id[i] = i;
    

        sz = new int[N];
        for (int i = 0; i < N; i++) {
        	
            sz[i] = 1;
        }
    
        count = N;
        id = new int[N];
        ht = new int[N];
        for (int i = 0; i < N; i++) {
            id[i] = i;
            ht[i] = 0;
        }
    }

	/*@ 
    
    
    
      ensures \result == count;
	@*/ 
     
    public int count() {
        return count;
    }

	/*@ 
  

	 
	
	 	requires ( 0 <= p && p < id.length );
	 	ensures \result == (find(p) == find(q));
	@*/ 
	 

    
    public /*@pure@*/ boolean connected  (int p, int q) {
        return find(p) == find(q);
    }

	/*@ 



   requires 0 <= p && p < id.length;
   requires 0 <= q && q < id.length;
   ensures connected(p,q);  
   ensures \old(connected(p,q)) ==> (count == \old(count));
   ensures \old(!connected(p,q)) ==> (count == \old(count) -1);
	@*/ 

   


    
    public void union  (int p, int q) {
        int i = find(p);
        int j = find(q);
        if (i == j)
            return;

        
        if      (ht[i] < ht[j]) id[i] = j;
        else if (ht[i] > ht[j]) id[j] = i;
        else
        {
            id[j] = i;
            ht[i]++;
        }
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

	/*@ 

  
    
	
	   requires 0 <= p && p < id.length;
	   ensures connected(\result, p);
	@*/  
	 
    public  /*@pure@*/ int find(int p) {
        while (p != id[p])
            p = id[p];
        return p;
    }

	
     private  int[] sz;

	
 
    private  int[] ht;

	

    
    public int id(int i) {
        return id[i];
    }


}
