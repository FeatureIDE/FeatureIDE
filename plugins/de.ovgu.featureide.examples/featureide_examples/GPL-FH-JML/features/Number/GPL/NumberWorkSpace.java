package GPL;

// **********************************************************************
   
public class NumberWorkSpace extends  WorkSpace 
{
	/*@spec_public@*/ int  vertexCounter;

    
    /*@ensures vertexCounter == 0;@*/
	/*@assignable vertexCounter; @*/
    public NumberWorkSpace( ) 
    {
        vertexCounter = 0;
    }

    /*@requires v != null;@*/
    /*@ensures (v.visited() == true) ==> (v.vertexNumber == vertexCounter+1);@*/
    /*@assignable vertexCounter; @*/
    public void preVisitAction( Vertex v )
    {
        // This assigns the values on the way in
        if ( v.visited != true )
        {
            v.VertexNumber = vertexCounter++;
        }
    }
}
