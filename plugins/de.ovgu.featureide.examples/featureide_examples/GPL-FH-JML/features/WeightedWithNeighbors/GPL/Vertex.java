public class Vertex {
    /*@requires end != null && end.adjacentNeighbors != null;@*/
    /*@ensures end.getLast().getWeight()==theWeight;@*/
    public void addWeight( Vertex end, int theWeight ) 
    {
        Neighbor the_neighbor = 
                ( Neighbor ) ( end.adjacentNeighbors ).removeLast();
        the_neighbor.weight = theWeight;
        ( end.adjacentNeighbors ).add( the_neighbor );
    }
    /*@requires \original && sourceNeighbor != null;@*/
    /*@ensures \original && end.getLast().getWeight()==theWeight;@*/
    public void adjustAdorns( Neighbor sourceNeighbor )
     {
        Neighbor targetNeighbor = 
                ( Neighbor )adjacentNeighbors.getLast();
        targetNeighbor.weight = sourceNeighbor.weight;
        original( sourceNeighbor );
    }
    
    public void display()
    {
        original();
    }

}
