package GPL;

// *************************************************************************

public class Edge {
    private int weight;

    public void EdgeConstructor( Vertex the_start,  Vertex the_end,
                int the_weight ) {
        EdgeConstructor( the_start,the_end );
        weight = the_weight;
    }

    // Constructor Loophole removed
    // public void EdgeConstructor($TEqn.Vertex the_start,
    //                    $TEqn.Vertex the_end) {
    // Super($TEqn.Vertex, $TEqn.Vertex).EdgeConstructor(the_start,the_end);
    // }

    public void adjustAdorns( EdgeIfc the_edge ) {
        setWeight(the_edge.getWeight());
        original( the_edge );
    }

    public void setWeight(int weight)
    {
        this.weight = weight;
    }

    public int getWeight()
    {
        return this.weight;
    }

    public void display() {
        System.out.print( " Weight=" + weight );
        original();
    }

}
