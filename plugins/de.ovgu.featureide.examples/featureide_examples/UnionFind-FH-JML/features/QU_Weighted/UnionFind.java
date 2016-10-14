public class UnionFind {
     private int[] sz;    // sz[i] = number of objects in subtree rooted at i
  
    // Create an empty union find data structure with N isolated sets.
    public UnionFind(int N) {

        sz = new int[N];
        for (int i = 0; i < N; i++) {
        	
            sz[i] = 1;
        }
    }

  


  
   // Replace sets containing p and q with their union.
    public void union(int p, int q) {
        int i = find(p);
        int j = find(q);
        if (i == j) return;

        // make smaller root point to larger one
        if   (sz[i] < sz[j]) { id[i] = j; sz[j] += sz[i]; }
        else                 { id[j] = i; sz[i] += sz[j]; }
        count--;
    }



}