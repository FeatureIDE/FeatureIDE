//layer BFS;

using System.Collections;

// *************************************************************************

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
        int     s, c;
        Vertex  v;
        Vertex  header;

        // Step 1: if preVisitAction is true or if we've already
        //         visited this node
        w.preVisitAction( ( Vertex ) this );

        if ( visited )
        {
            return;
        }

        // Step 2: Mark as visited, put the unvisited neighbors in the queue
        //     and make the recursive call on the first element of the queue
        //     if there is such if not you are done
        visited = true;

        // Step 3: do postVisitAction now, you are no longer going through the
        // node again, mark it as black
        w.postVisitAction( ( Vertex ) this );

        // enqueues the vertices not visited
        for ( Iterator<Vertex> vxiter = GetNeighbors( ); vxiter.hasNext( ); )
        {
            v = vxiter.next( );

            // if your neighbor has not been visited then enqueue
            if ( !v.visited ) 
            {
                GlobalVarsWrapper.Queue.Add( v );
            }

        } // end of for

        // while there is something in the queue
        while( GlobalVarsWrapper.Queue.Count!= 0 )
        {
            header = ( Vertex ) GlobalVarsWrapper.Queue[0];
            GlobalVarsWrapper.Queue.RemoveAt( 0 );
            header.nodeSearch( w );
        }
    } // of bfsNodeSearch

    public void display( ) 
    {
        if ( visited )
            System.Console.Out.Write( "  visited " );
        else
            System.Console.Out.WriteLine( " !visited " );
        original( );
    }
}
