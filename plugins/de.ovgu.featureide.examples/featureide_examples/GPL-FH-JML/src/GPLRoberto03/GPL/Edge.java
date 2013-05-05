package GPL; 

import java.util.LinkedList; 



public   class  Edge  extends Neighbor  implements EdgeIfc {
	
    public /*@spec_public@*/ Vertex start;

	/*@ 

    requires the_start != null && the_end != null;
    ensures this.start == the_start && this.end == the_end; @*/
	
    public void EdgeConstructor( Vertex the_start, Vertex the_end )
    {
        start = the_start;
        end = the_end;
    }


	

     private void  adjustAdorns__wrappee__DFS  ( EdgeIfc the_edge ) 
    {
    }

	/*@ 

    
    
    
    
    
    requires the_edge != null;
    ensures \original && this.getWeight() == the_edge.getWeight(); @*/
	
    public void adjustAdorns( EdgeIfc the_edge ) {
        setWeight(the_edge.getWeight());
        adjustAdorns__wrappee__DFS( the_edge );
    }

	/*@ 

    ensures this.weight == weight; @*/
	 
    public void setWeight  (int weight)
    {
        this.weight = weight;
    }

	/*@ 

    ensures \result == this.weight; @*/
	
    public /*@pure@*/ int getWeight  ()
    {
        return this.weight;
    }


	
    
    
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


	

     private void  display__wrappee__DFS  ( ) 
    {
        System.out.println( " start=" + start.getName() + " end=" + end.getName( ) );
    }


	

    public void display() {
        System.out.print( " Weight=" + weight );
        display__wrappee__DFS();
    }

	
    private /*@spec_public@*/ int weight;

	/*@ 
    
    requires the_start != null && the_end != null && the_weight != null; 
    ensures this.start == the_start && end == this.the_end && this.weight == the_weight; @*/
	
    public void EdgeConstructor( Vertex the_start,  Vertex the_end,
                int the_weight ) {
        EdgeConstructor( the_start,the_end );
        weight = the_weight;
    }


}
