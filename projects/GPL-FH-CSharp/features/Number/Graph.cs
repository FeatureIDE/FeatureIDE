
// ***********************************************************************
   
public class Graph //refines
{
    // Executes Number Vertices
    public void run( Vertex s )
     {
       	System.Console.Out.WriteLine("Number");
        NumberVertices( );
        original( s );
    }

    public void NumberVertices( ) 
    {
        GraphSearch( new NumberWorkSpace( ) );
    }
}
