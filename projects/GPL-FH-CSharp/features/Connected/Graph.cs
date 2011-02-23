//layer Connected;

// *****************************************************************
   
public class Graph //refines
{
    // Executes Connected Components
    public void run( Vertex s )
    {
	     	System.Console.Out.WriteLine("Connected");
        ConnectedComponents( );
        original( s );
    }

    public void ConnectedComponents( ) 
    {
        GraphSearch( new RegionWorkSpace( ) );
    }
}
