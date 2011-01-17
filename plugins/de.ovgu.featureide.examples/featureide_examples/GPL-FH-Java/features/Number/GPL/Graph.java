package GPL;

// ***********************************************************************
   
public class Graph 
{
    // Executes Number Vertices
    public void run( Vertex s )
     {
       	System.out.println("Number");
        NumberVertices( );
        original( s );
    }

    public void NumberVertices( ) 
    {
        GraphSearch( new NumberWorkSpace( ) );
    }
}
