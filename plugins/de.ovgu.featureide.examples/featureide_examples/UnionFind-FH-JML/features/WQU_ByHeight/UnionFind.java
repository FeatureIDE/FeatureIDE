public class UnionFind {
 
    private int[] ht;   // ht[i] = height of subtree rooted at i

    // Create an empty union find data structure with N isolated sets.
    public UnionFind(int N) {
        count = N;
        id = new int[N];
        ht = new int[N];
        for (int i = 0; i < N; i++) {
            id[i] = i;
            ht[i] = 0;
        }
    }

    // return id[i]
    public int id(int i) {
        return id[i];
    }

   


    // Replace sets containing p and q with their union.
    public void union(int p, int q) {
        int i = find(p);
        int j = find(q);
        if (i == j)
            return;

        // make smaller root point to larger one
        if      (ht[i] < ht[j]) id[i] = j;
        else if (ht[i] > ht[j]) id[j] = i;
        else
        {
            id[j] = i;
            ht[i]++;
        }
        count--;
    }

  

}
