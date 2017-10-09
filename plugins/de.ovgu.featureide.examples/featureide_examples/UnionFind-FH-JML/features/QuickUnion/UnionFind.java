
public class UnionFind{

  
    // return root of component corresponding to element p
	/*@
	   requires 0 <= p && p < id.length;
	   ensures connected(\result, p); 
	 */
    public  /*@pure@*/ int find(int p) {
        while (p != id[p])
            p = id[p];
        return p;
    }
  

	 // are elements p and q in the same component?
	/*@
	 @ ensures \result == (find(p) == find(q));
	 @ assignable \nothing;
	 @*/
    public boolean connected(int p, int q) {
        return find(p) == find(q);
    }

    // merge components containing p and q
    public void union(int p, int q) {
        int i = find(p);
        int j = find(q);
        if (i == j) return;
        id[i] = j; 
        count--;
    }

    

}