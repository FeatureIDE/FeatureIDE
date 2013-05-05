package GPL;

// ***********************************************************************
 
public class Graph {
    // Adds an edge with weights
	/*@requires start != null && end != null && weight != null;@*/
	/*@ensures findsEdge(start,end) != null && findsEdge(start, end).getWeight()==weight;@*/
    public void addAnEdge( Vertex start,  Vertex end, int weight )
    {
        addEdge( start, new  Neighbor( end, weight ) );
    }
      
    /*@requires start != null && theNeighbor != null;@*/
    /*@ensures \original;@*/
    /*@ensures !isDirected ==> (theNeighbor.neighbor.getWeight()==theNeighbor.weight);@*/
    public void addEdge( Vertex start,  Neighbor theNeighbor )
    {
        original( start,theNeighbor );
          
        // At this point the edges are added.
        // If there is an adorn like weight it has to be added to
        // the neighbor already present there
        if ( isDirected==false ) 
      {
            // It has to add ONLY the weight object to the neighbor
            Vertex end = theNeighbor.neighbor;
            end.addWeight( end,theNeighbor.weight );
        
        } // of else
    }
    
    public void display() 
    {
        original();
    }

}
