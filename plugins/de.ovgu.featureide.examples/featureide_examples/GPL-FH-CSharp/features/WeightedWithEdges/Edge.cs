//layer Weighted;

// *************************************************************************

public class Edge {//refines
    private int weight;

    public void EdgeConstructor( Vertex the_start,  Vertex the_end,
                int the_weight ) {
        EdgeConstructor( the_start,the_end );
        weight = the_weight;
    }

    // Constructor Loophole Removed
    // public void EdgeConstructor($TEqn.Vertex the_start,
    //                    $TEqn.Vertex the_end) {
    // Super($TEqn.Vertex, $TEqn.Vertex).EdgeConstructor(the_start,the_end);
    // }

    public void adjustAdorns( EdgeIfc the_edge ) {
        setWeight(the_edge.GetWeight());
        original( the_edge );
    }

    public void setWeight(int weight)
    {
        this.weight = weight;
    }

    public int GetWeight()
    {
        return this.weight;
    }

    public void display() {
        System.Console.Out.Write( " Weight=" + weight );
        original();
    }

}
