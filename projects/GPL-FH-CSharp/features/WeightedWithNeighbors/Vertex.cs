//layer Weighted;

// of Graph
 
// *************************************************************************
 
public class Vertex {//refines
    public void AddWeight( Vertex end, int theWeight ) 
    {
        Neighbor the_neighbor =
                (Neighbor)(end.adjacentNeighbors[end.adjacentNeighbors.Count - 1]);
        end.adjacentNeighbors.RemoveAt(end.adjacentNeighbors.Count - 1);

        the_neighbor.weight = theWeight;
        ( end.adjacentNeighbors ).Add( the_neighbor );
    }
    
    public void adjustAdorns( Neighbor sourceNeighbor )
     {
        Neighbor tarGetNeighbor =
                (Neighbor)adjacentNeighbors[adjacentNeighbors.Count - 1];
        tarGetNeighbor.weight = sourceNeighbor.weight;
        original( sourceNeighbor );
    }
    
    public void display()
    {
        original();
    }

}
