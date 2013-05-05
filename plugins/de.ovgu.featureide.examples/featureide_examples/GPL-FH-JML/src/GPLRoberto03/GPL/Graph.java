package GPL; 
import java.util.LinkedList; 
import java.util.Iterator; 
import java.util.Collections; 
import java.util.Comparator; 


import java.util.HashMap; 
import java.util.Map; 

import java.lang.Integer; 



public   class  Graph {
	
    private LinkedList vertices;

	
    private LinkedList edges;

	
    public static final boolean isDirected = false;

	

    
    private Map verticesMap;


	


    public Graph() {
        vertices = new LinkedList();
        edges = new LinkedList();

	  
        verticesMap = new HashMap( );

    }


	

    
     private void  run__wrappee__TestProg  ( Vertex s ) {}


	
    
     private void  run__wrappee__Number  ( Vertex s )
     {
       	System.out.println("Number");
        NumberVertices( );
        run__wrappee__TestProg( s );
    }

	/*@ 
    
	requires \original;
	 ensures \original; @*/
	
	 
     private void  run__wrappee__Connected  ( Vertex s )
    {
	     	System.out.println("Connected");
        ConnectedComponents( );
        run__wrappee__Number( s );
    }

	/*@ 

    
	requires ( \original );
	 ensures ( \original ); @*/
	
	 
     private void  run__wrappee__Cycle  ( Vertex s )
     {
        System.out.println( "Cycle? " + CycleCheck() );
        run__wrappee__Connected( s );
    }

	/*@ 

    
	requires ( \original );
	 ensures ( \original ); @*/
	

    
    public void run( Vertex s )
     {
     	System.out.println("MSTKruskal");
        Graph gaux = Kruskal();

        gaux.display();

        run__wrappee__Cycle( s );
    }


	

    public void sortEdges(Comparator c) {
        Collections.sort(edges, c);
    }


	
	/*@public model pure boolean isSorted(LinkedList list) {
 	return true;
 	}@*/

	/*@ 
     requires c != null;
    ensures isSorted(vertices); @*/
	 
    public void sortVertices(Comparator c) {
        Collections.sort(vertices, c);
    }

	/*@ 

    
	 requires v1 != null && v2 != null; 
	 ensures \result.getOtherVertex(v1)==v2 && \result.getOtherVertex(v2)==v1; 
     ensures findsEdge(start,getOtherVertex(theNeighbor)) != null && findsEdge(start, getOtherVertex(theNeighbor)); @*/
	
    public EdgeIfc addEdge(Vertex start,  Vertex end) {
        Edge theEdge = new  Edge();
        theEdge.EdgeConstructor( start, end );
        edges.add( theEdge );
        start.addNeighbor( new  Neighbor( end, theEdge ) );
        end.addNeighbor( new  Neighbor( start, theEdge ) );

        return theEdge;
    }


	

    protected void addVertex( Vertex v ) {
        vertices.add( v );

	  
	  verticesMap.put( v.name, v );

    }


	

    
    public  /*@pure@*/ Vertex findsVertex( String theName ) {
        Vertex theVertex;

        
        if ( theName==null )
            return null;

	  








	  
	  return ( Vertex ) verticesMap.get( theName );

    }

	/*@ 

     ensures \result != null; @*/
	 
    public VertexIter getVertices() {
        return new VertexIter() {
                private Iterator iter = vertices.iterator();
                public Vertex next() { return (Vertex)iter.next(); }
                public boolean hasNext() { return iter.hasNext(); }
            };
    }


	

    public EdgeIter getEdges() {
        return new EdgeIter() {
                private Iterator iter = edges.iterator();
                public EdgeIfc next() { return (EdgeIfc)iter.next(); }
                public boolean hasNext() { return iter.hasNext(); }
            };
    }


	

    
    public  /*@pure@*/ EdgeIfc findsEdge( Vertex theSource,
                    Vertex theTarget )
       {
        EdgeIfc theEdge;

	  
      
        for( EdgeIter edgeiter = theSource.getEdges(); edgeiter.hasNext(); )
         {
            theEdge = edgeiter.next();
            if ( ( theEdge.getStart().getName().equals( theSource.getName() ) &&
                  theEdge.getEnd().getName().equals( theTarget.getName() ) ) ||
                 ( theEdge.getStart().getName().equals( theTarget.getName() ) &&
                  theEdge.getEnd().getName().equals( theSource.getName() ) ) )
                return theEdge;
        }
        return null;
    }


	

    public void display() {
        System.out.println( "******************************************" );
        System.out.println( "Vertices " );
        for ( VertexIter vxiter = getVertices(); vxiter.hasNext() ; )
            vxiter.next().display();

        System.out.println( "******************************************" );
        System.out.println( "Edges " );
        for ( EdgeIter edgeiter = getEdges(); edgeiter.hasNext(); )
            edgeiter.next().display();

        System.out.println( "******************************************" );
    }


	

    public void NumberVertices( ) 
    {
        GraphSearch( new NumberWorkSpace( ) );
    }


	

    public void ConnectedComponents( ) 
    {
        GraphSearch( new RegionWorkSpace( ) );
    }


	
              
    public boolean CycleCheck() {
        CycleWorkSpace c = new CycleWorkSpace( isDirected );
        GraphSearch( c );
        return c.AnyCycles;
    }


	

    public  Graph Kruskal() {

        
        LinkedList A = new LinkedList();

        
        

        for ( VertexIter vxiter = getVertices(); vxiter.hasNext(); )
        {
            Vertex v = vxiter.next();
            v.representative = v; 
            v.members = new LinkedList(); 
        }

        
        
        
        LinkedList Vneighbors = new LinkedList();
        

        
        sortEdges(
            new Comparator() {
                public int compare( Object o1, Object o2 )
                 {
                Edge e1 = ( Edge )o1;
                Edge e2 = ( Edge )o2;
                if ( e1.getWeight() < e2.getWeight() )
                    return -1;
                if ( e1.getWeight() == e2.getWeight() )
                    return 0;
                return 1;
                }
        } );

        
        Vertex vaux, urep, vrep;

        for( EdgeIter edgeiter = getEdges(); edgeiter.hasNext(); )
        {
            
            EdgeIfc e1 = edgeiter.next();
            Vertex u = e1.getStart();
            Vertex v = e1.getEnd();

            if ( ! ( v.representative.getName() ).equals( u.representative.getName() ) )
              {
                
                A.add( e1 );

                
                urep = u.representative;
                vrep = v.representative;

                if ( ( urep.members ).size() > ( vrep.members ).size() )
                    { 
                    for( int j=0; j< ( vrep.members ).size(); j++ )
                          {
                        vaux = ( Vertex ) ( vrep.members ).get( j );
                        vaux.representative = urep;
                        ( urep.members ).add( vaux );
                    }
                    v.representative = urep;
                    vrep.representative = urep;
                    ( urep.members ).add( v );
                    if ( !v.equals( vrep ) )
                        ( urep.members ).add( vrep );
                    ( vrep.members ).clear();
                }
                else
                     { 
                    for( int j=0; j< ( urep.members ).size(); j++ )
                           {
                        vaux = ( Vertex ) ( urep.members ).get( j );
                        vaux.representative = vrep;
                        ( vrep.members ).add( vaux );
                    }
                    u.representative = vrep;
                    urep.representative = vrep;
                    ( vrep.members ).add( u );
                    if ( !u.equals( urep ) )
                        ( vrep.members ).add( urep );
                    ( urep.members ).clear();

                } 

            } 

        } 

        
        
        String theName;
        Graph newGraph = new  Graph();

        
        for ( VertexIter vxiter = getVertices(); vxiter.hasNext(); )
      {
            theName = vxiter.next().getName();
            newGraph.addVertex( new  Vertex().assignName( theName ) );
        }

        
        Vertex theStart, theEnd;
        Vertex theNewStart, theNewEnd;
        EdgeIfc   theEdge;

        
        
        
        for( int i=0; i<A.size(); i++ )
       {
            
            theEdge = ( Edge )A.get( i );
            theStart = theEdge.getStart();
            theEnd = theEdge.getEnd();

            
            theNewStart = newGraph.findsVertex( theStart.getName() );
            theNewEnd = newGraph.findsVertex( theEnd.getName() );

            
            
            
            
            


            Edge theNewEdge = ( Edge ) newGraph.addEdge( theNewStart, theNewEnd );
            theNewEdge.adjustAdorns( ( Edge )  theEdge );
        }
        return newGraph;

    }


	
    public void GraphSearch( WorkSpace w ) 
    {
        
        VertexIter vxiter = getVertices( );
        if ( vxiter.hasNext( ) == false )
        {
            return; 
        }

        
        while( vxiter.hasNext( ) ) 
        {
            Vertex v = vxiter.next( );
            v.init_vertex( w );
        }

        
        for( vxiter = getVertices( ); vxiter.hasNext( ); ) 
        {
            Vertex v = vxiter.next( );
            if ( !v.visited ) 
            {
                w.nextRegionAction( v );
                v.nodeSearch( w );
            }
        } 
    }


}
