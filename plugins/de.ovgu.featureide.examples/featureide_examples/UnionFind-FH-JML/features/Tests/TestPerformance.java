import org.junit.*;



public class TestPerformance{
	private static final String TEST_DATA_LOCATION = "TestData";

	@Test
	public void testSmallData() {
				testData(TEST_DATA_LOCATION + "/tinyUF.txt");
	}
	@Test
	public void testMediumData() {
			testData(TEST_DATA_LOCATION + "/mediumUF.txt");
	}
	@Test
	public void testLargeData() {
			testData(TEST_DATA_LOCATION + "/largeUF.txt");
	}
	private void testData(String filename){
		In in = new In(filename);
        int N = in.readInt();
        UnionFind uf = new UnionFind(N);

 
        while (!in.isEmpty()) {
            int p = in.readInt();
            int q = in.readInt();
            if (uf.connected(p, q)) continue;
            uf.union(p, q);
           
        }
   
        
	}
}
