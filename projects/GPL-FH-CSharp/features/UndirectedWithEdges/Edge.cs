//layer Undirected;

using System.Collections;

// *************************************************************************

public class Edge : Neighbor, EdgeIfc // hier: superklasse UND superinterface (implements und extends in einem ":")
{
    public Vertex start;

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

    public int GetWeight( ) 
    { 
        return 0; 
    }

    public Vertex GetOtherVertex( Vertex vertex )
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

    public Vertex GetStart( )
    {
        return start;
    }

    public Vertex GetEnd( )
    {
        return end;
    }

    public void display( ) 
    {
        System.Console.Out.WriteLine( " start=" + start.GetName() + " end=" + end.GetName( ) );
    }
}
