//layer Weighted;

// ***********************************************************************
 
public class Graph {//refines
    // Adds an edge with weights
    public void AddAnEdge( Vertex start,  Vertex end, int weight )
    {
        AddEdge( start, new  Neighbor( end, weight ) );
    }
      
    public void AddEdge( Vertex start,  Neighbor theNeighbor )
    {
        original( start,theNeighbor );
          
        // At this point the edges are Added.
        // If there is an adorn like weight it has to be Added to
        // the neighbor already present there
        if ( isDirected==false ) 
      {
            // It has to Add ONLY the weight object to the neighbor
            Vertex end = theNeighbor.neighbor;
            end.AddWeight( end,theNeighbor.weight );
        
        } // of else
    }
    
    public void display() 
    {
        original();
    }

}
