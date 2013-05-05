package GPL;

// end of Vertex class
 
  // *************************************************************************
  
public class Neighbor {
    public int weight;
    /*@requires theNeighbor != null;@*/
    /*@ensures  this.neighbor == theNeighbor && this.getWeight == theWeight;@*/
    public Neighbor( Vertex theNeighbor, int theWeight ) {
        NeighborConstructor( theNeighbor, theWeight );
    }
    
    /*@requires theNeighbor != null;@*/
    /*@ensures  this.neighbor == theNeighbor && this.getWeight == theWeight;@*/
    public void NeighborConstructor( Vertex theNeighbor, int theWeight )
    {
        NeighborConstructor( theNeighbor );
        weight = theWeight;
    }

    public void display()
    {
        System.out.print( " Weight = " + weight + " " );
        original();
    }
    /*@ensures this.weight == weight;@*/
    public void setWeight(int weight)
    {
        this.weight = weight;
    }

    /*@ensures \result == this.weight;@*/
    public /*@pure@*/ int getWeight()
    {
        return this.weight;
    }


}
