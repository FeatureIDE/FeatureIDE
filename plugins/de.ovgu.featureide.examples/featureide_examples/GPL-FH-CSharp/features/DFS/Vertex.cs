/*layer DFS;

  // *************************************************************************
*/
public class Vertex //refines
{
    public bool visited;

    public void VertexConstructor( ) 
    {
        original( );
        visited = false;
    }

    public void init_vertex( WorkSpace w ) 
    {
        visited = false;
        w.init_vertex( ( Vertex ) this );
    }

    public void nodeSearch( WorkSpace w ) 
    {
        Vertex v;

        // Step 1: Do preVisitAction.
        //            If we've already visited this node return
        w.preVisitAction( ( Vertex ) this );

        if ( visited )
            return;

        // Step 2: else remember that we've visited and
        //         visit all neighbors
        visited = true;

        for ( Iterator<Vertex>  vxiter = GetNeighbors(); vxiter.hasNext(); ) 
        {
            v = vxiter.next( );
            w.checkNeighborAction( ( Vertex ) this, v );
            v.nodeSearch( w );
        }

        // Step 3: do postVisitAction now
        w.postVisitAction( ( Vertex ) this );
    } // of dftNodeSearch

    public void display( ) {
        if ( visited )
            System.Console.Out.Write( "  visited" );
        else
            System.Console.Out.WriteLine( " !visited " );
        original( );
    }
}
