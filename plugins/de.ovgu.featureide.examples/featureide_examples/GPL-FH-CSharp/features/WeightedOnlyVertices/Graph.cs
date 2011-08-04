//layer Weighted;

using System.Collections;

// ************************************************************
 
public class Graph {//refines
    // Adds an edge with weights
    public void AddAnEdge( Vertex start,  Vertex end, int weight )
   {
        AddEdge( start,end, weight );
    }
 
    public void AddEdge( Vertex start,  Vertex end, int weight )
   {
        AddEdge( start,end ); // Adds the start and end as adjacent
        start.AddWeight( weight ); // the direction layer takes care of that
                
        // if the graph is undirected you have to include 
        // the weight of the edge coming back
        if ( isDirected==false )
            end.AddWeight( weight );
    }
    
    public void display() 
   {
        original();
    }

}
