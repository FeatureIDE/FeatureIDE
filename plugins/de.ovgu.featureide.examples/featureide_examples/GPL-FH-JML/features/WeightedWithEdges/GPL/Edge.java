package GPL;

// *************************************************************************

public class Edge {
    private /*@spec_public@*/ int weight;
    
    /*@requires the_start != null && the_end != null && the_weight != null; @*/
    /*@ensures this.start == the_start && end == this.the_end && this.weight == the_weight;@*/
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
    /*@requires the_edge != null;@*/
    /*@ensures \original && this.getWeight() == the_edge.getWeight();@*/
    public void adjustAdorns( EdgeIfc the_edge ) {
        setWeight(the_edge.getWeight());
        original( the_edge );
    }

    /*@ensures this.weight == weight; @*/
    public void setWeight(int weight)
    {
        this.weight = weight;
    }

    /*@ensures \result == this.weight;@*/
    public /*@pure@*/ int getWeight()
    {
        return this.weight;
    }

    public void display() {
        System.out.print( " Weight=" + weight );
        original();
    }

}
