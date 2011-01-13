package GPL;

// end of Vertex class
 
  // *************************************************************************
  
public class Neighbor {
    public int weight;

    public Neighbor( Vertex theNeighbor, int theWeight ) {
        NeighborConstructor( theNeighbor, theWeight );
    }

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

    public void setWeight(int weight)
    {
        this.weight = weight;
    }

    public int getWeight()
    {
        return this.weight;
    }


}
