package GPL; 

import java.util.Iterator; 
import java.util.LinkedList; 

import java.lang.Integer; 
import java.util.Collections; 
import java.util.Comparator; 

  

public   class  Vertex {
	
    public /*@spec_public@*/ LinkedList  neighbors;

	
    public /*@spec_public@*/ String  name;


	

    public Vertex( ) 
    {
        VertexConstructor( );
    }

	/*@ 
    ensures name == null && adjacentNeighbors != null; @*/
	
     private void  VertexConstructor__wrappee__MSTKruskal  ( ) 
    {
        name      = null;
        neighbors = new LinkedList( );
    }

	/*@ 

    ensures original && visited == false; @*/
	
    public void VertexConstructor( ) 
    {
        VertexConstructor__wrappee__MSTKruskal( );
        visited = false;
    }

	/*@ 

     requires name != null;
    ensures this.name == name;
    ensures \result == this; @*/
	 
    public  Vertex assignName( String name ) 
    {
        this.name = name;
        return ( Vertex ) this;
    }

	/*@ 
     ensures \result == this.name; @*/
	 
    public String getName( )
    {
        return this.name;
    }

	/*@ 

     ensures \result == this.neighbors; @*/
	
    public LinkedList getNeighborsObj( )
    {
 	  return neighbors;
    }


	


    public VertexIter getNeighbors( )
    {
        return new VertexIter( )
        {
            private Iterator iter = neighbors.iterator( );
            public Vertex next( ) 
            { 
              return ( ( Neighbor )iter.next( ) ).end; 
            }
            public boolean hasNext( ) 
            { 
              return iter.hasNext( ); 
            }
        };
    }


	

     private void  display__wrappee__TestProg  ( ) 
    {
        System.out.print( " Node " + name + " connected to: " );

        for ( VertexIter vxiter = getNeighbors( ); vxiter.hasNext( ); )
        {
            System.out.print( vxiter.next().getName() + ", " );
        }

        System.out.println( );
    }


	

     private void  display__wrappee__Number  ( ) 
    {
        System.out.print( " # "+ VertexNumber + " " );
        display__wrappee__TestProg( );
    }


	

     private void  display__wrappee__Connected  ( ) 
    {
        System.out.print( " comp# "+ componentNumber + " " );
        display__wrappee__Number( );
    }


	 
      
     private void  display__wrappee__Cycle  () {
        System.out.print( " VertexCycle# " + VertexCycle + " " );
        display__wrappee__Connected();
    }


	

     private void  display__wrappee__MSTKruskal  () {
        if ( representative == null )
            System.out.print( "Rep null " );
        else
            System.out.print( " Rep " + representative.getName() + " " );
        display__wrappee__Cycle();
    }


	 

    public void display( ) {
        if ( visited )
            System.out.print( "  visited" );
        else
            System.out.println( " !visited " );
        display__wrappee__MSTKruskal( );
    }

	/*@       




    requires n != null;
    ensures neighbors.getLast()==n; @*/
	
    public void addNeighbor( Neighbor n ) 
    {
        neighbors.add( n );
    }


	

    public EdgeIter getEdges( )
    {
        return new EdgeIter( )
        {
            private Iterator iter = neighbors.iterator( );
            public EdgeIfc next( ) 
            { 
              return ( ( EdgeIfc ) ( ( Neighbor )iter.next( ) ).edge );
            }
            public boolean hasNext( ) 
            { 
              return iter.hasNext( ); 
            }
        };
    }

	
    public  /*@spec_public@*/ int  VertexNumber;

	
    public int componentNumber;

	
    public int VertexCycle;

	
    public int VertexColor;

	
    public /*@spec_public@*/ Vertex  representative;

	
    public /*@spec_public@*/ LinkedList  members;

	
    public /*@spec_public@*/ boolean visited;

	/*@ 
    requires w != null; @*/
	
    public void init_vertex( WorkSpace w ) 
    {
        visited = false;
        w.init_vertex( ( Vertex ) this );
    }

	/*@ 
    requires w != null; @*/
	
    public void nodeSearch( WorkSpace w ) 
    {
        Vertex v;

        
        
        w.preVisitAction( ( Vertex ) this );

        if ( visited )
            return;

        
        
        visited = true;

        for ( VertexIter  vxiter = getNeighbors(); vxiter.hasNext(); ) 
        {
            v = vxiter.next( );
            w.checkNeighborAction( ( Vertex ) this, v );
            v.nodeSearch( w );
        }

        
        w.postVisitAction( ( Vertex ) this );
    }


}
