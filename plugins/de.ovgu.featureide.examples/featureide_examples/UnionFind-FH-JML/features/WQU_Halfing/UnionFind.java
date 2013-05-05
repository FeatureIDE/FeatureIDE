public class UnionFind {
   
	 // return component identifier for component containing p
    public int find(int p) {
        while (p != id[p]) {
            id[p] = id[id[p]];    // path compression by halving
            p = id[p];
        }
        return p;
    }

  




}