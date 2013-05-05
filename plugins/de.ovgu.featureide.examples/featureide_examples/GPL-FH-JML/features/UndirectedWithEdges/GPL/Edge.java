package GPL;

import java.util.LinkedList;

// *************************************************************************

public class Edge extends Neighbor implements EdgeIfc 
{
    public /*@spec_public@*/ Vertex start;

    /*@requires the_start != null && the_end != null;@*/
    /*@ensures this.start == the_start && this.end == the_end;@*/
    public void EdgeConstructor( Vertex the_start, Vertex the_end )
    {
        start = the_start;
        end = the_end;
    }

    public void adjustAdorns( EdgeIfc the_edge ) 
    {
    }

    public void setWeight(int weight) 
    {
    }

    public /*@pure@*/ int getWeight( ) 
    { 
        return 0; 
    }
    
    //specification enherited
    public Vertex getOtherVertex( Vertex vertex )
    {
        if( vertex == start )
        { 
            return end;
        }
        else if(vertex == end)
        { 
            return start;
        }
        else
        { 
            return null;
        }
    }

    public /*@pure@*/ Vertex getStart( )
    {
        return start;
    }

    public /*@pure@*/ Vertex getEnd( )
    {
        return end;
    }

    public void display( ) 
    {
        System.out.println( " start=" + start.getName() + " end=" + end.getName( ) );
    }
}
