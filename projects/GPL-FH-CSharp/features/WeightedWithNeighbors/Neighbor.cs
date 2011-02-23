//layer Weighted;

// end of Vertex class
 
  // *************************************************************************
  
public class Neighbor {//refines
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
        System.Console.Out.Write( " Weight = " + weight + " " );
        original();
    }

    public void setWeight(int weight)
    {
        this.weight = weight;
    }

    public int GetWeight()
    {
        return this.weight;
    }


}
