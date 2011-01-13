package GPL;

// *****************************************************************
   
public class Graph 
{
    // Executes Connected Components
    public void run( Vertex s )
    {
	     	System.out.println("Connected");
        ConnectedComponents( );
        original( s );
    }

    public void ConnectedComponents( ) 
    {
        GraphSearch( new RegionWorkSpace( ) );
    }
}
