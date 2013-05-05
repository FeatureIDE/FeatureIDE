package GPL;

// *****************************************************************
   
public class Graph 
{
    // Executes Connected Components
	/*@requires \original;
	 ensures \original;
	 @*/
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
