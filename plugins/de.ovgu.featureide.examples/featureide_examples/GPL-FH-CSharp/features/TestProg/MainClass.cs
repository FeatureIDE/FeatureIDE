class MainClass {
    public static void Main( string[] args ) {

        Graph g = new  Graph();

        Vertex pre = null;
        for(int i = 0; i < 10; i++) {
            Vertex v = new Vertex();
            v.assignName("vertex " + i);
            g.AddVertex(v);
            if(pre != null) {
                g.AddEdge(pre, v);
            }
            pre = v;
        }
		g.run(g.GetVertices().next());
        g.display();
        System.Console.In.Read();
    }
}
