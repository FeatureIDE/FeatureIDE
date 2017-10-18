
public class UnionFind{
/*@spec_public*/   private int[] id;    // id[i] = parent of i
/*@spec_public*/   private int count;   // number of components
    
    // instantiate N isolated components 0 through N-1
    /*@
       requires N > 0;
       ensures count == N; 
	   ensures (\forall int i; 0 <= i && i < N;
id[i] == i);
	   assignable count, id, id[*];
     */
    public UnionFind(int N) {
        count = N;
        id = new int[N];
        for (int i = 0; i < N; i++)
        id[i] = i;
    }
    
    // return number of connected components
    /*@
      ensures \result == count;
      assignable \nothing;
     */
    public int count() {
        return count;
    }
	/*@ \consecutive_contract
 	 @ requires 0 <= p && p < id.length; 
	 @*/
	public /*@pure@*/ boolean connected(int p, int q) {
	   
	}

// merge components containing p and q
/*@
   requires 0 <= p && p < id.length;
   requires 0 <= q && q < id.length;
   ensures connected(p,q);  
   ensures \old(connected(p,q)) ==> (count == \old(count));
   ensures \old(!connected(p,q)) ==> (count == \old(count) -1);
   assignable count;
 */
public void union(int p, int q) {
 
}
	    public static void main(String[] args) {
	     	
	    	In in = new In("TestData/mediumUF.txt");
	        int N = in.readInt();
	        Stopwatch s = new Stopwatch();
	        UnionFind uf = new UnionFind(N);
	        
	        // read in a sequence of pairs of integers (each in the range 0 to N-1),
	         // calling find() for each pair: If the members of the pair are not already
	        // call union() and print the pair.
	        while (!in.isEmpty()) {
	            int p = in.readInt();
	            int q = in.readInt();
	            if (uf.connected(p, q)) continue;
	            uf.union(p, q);
	            //StdOut.println(p + " " + q);
	        }
	        StdOut.println(s.elapsedTime() + " time");
	        uf.count();
	        StdOut.println(uf.count() + " components");
	   
	    }

	


}
