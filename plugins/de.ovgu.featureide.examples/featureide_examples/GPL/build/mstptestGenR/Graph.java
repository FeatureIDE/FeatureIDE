package mstptestGenR;

import java.util.Comparator;
import java.util.Collections;

import java.io.*;



// define shell of a Graph class

abstract class Graph$$Base {
   LinkedList vertices;
   Graph$$Base(){
     vertices = new LinkedList();
   }

   public VertexIter getVertices( ) {
      return new VertexIter(((Graph) this));
   }

   public void sortVertices(Comparator c) {
      Collections.sort(vertices, c);
   }

   // methods whose bodies will be overridden later
   EdgeIfc addEdge( Vertex v1, Vertex v2 ) { return null; }
   Vertex findsVertex( String name ) { return null; }
   void display() { }
   void addVertex( Vertex v ) { }
}



// adds utilities for reading files
// not really clear why these methods belong to Graph
// probably because this methods are easier to reuse
// if attached to Graph

abstract class Graph$$Benchmark extends  Graph$$Base 
{
    public Reader inFile; // File handler for reading
    public static int ch; // Character to read/write

    // timings
    static long last = 0, current = 0, accum = 0;

    public void runBenchmark( String FileName ) throws IOException
    {
        try
        {
            inFile = new FileReader( FileName );
        }
        catch ( IOException e )
        {
            System.out.println( "Your file " + FileName + " cannot be read" );
        }
    }

    public void stopBenchmark( ) throws IOException
    {
        inFile.close( );
    }

    public int readNumber( ) throws IOException
    {
        int index = 0;
        char[ ] word = new char[ 80 ];
        int ch = 0;

        ch = inFile.read( );
        while( ch==32 )
        {
            ch = inFile.read( ); // skips extra whitespaces
        }

        while( ch != -1 && ch != 32 && ch != 10 ) // while it is not EOF, WS, NL
        {
            word[ index++ ] = ( char )ch;
            ch = inFile.read( );
        }
        word[ index ] = 0;

        String theString = new String( word );

        theString = new String( theString.substring( 0,index ) ).trim( );
        return Integer.parseInt( theString,10 );
    }

    public static void startProfile( )
    {
        accum = 0;
        current = System.currentTimeMillis( );
        last = current;
    }

    public static void stopProfile( )
    {
        current = System.currentTimeMillis( );
        accum = accum + ( current - last );
    }

    public static void resumeProfile( )
    {
        current = System.currentTimeMillis( );
        last = current;
    }

    public static void endProfile( )
     {
        current = System.currentTimeMillis( );
        accum = accum + ( current-last );
        System.out.println( "Time elapsed: " + accum + " milliseconds" );
    }
      // inherited constructors


   Graph$$Benchmark (  ) { super(); }
}

//created on: Sat Dec 04 12:51:45 CST 2004

 abstract class Graph$$Prog extends  Graph$$Benchmark  {
    // method is extended later
    public void run( Vertex v ) { }
      // inherited constructors


   Graph$$Prog (  ) { super(); }
}

//created on: Sat Dec 04 16:05:48 CST 2004

 abstract class Graph$$UndirectedCommon extends  Graph$$Prog  {
    public static final boolean isDirected = false;
    protected Map verticesMap = new HashMap( );

    public void addVertex( Vertex v ) {
      vertices.add( v );
      verticesMap.put( v.name, v );
    }

    // Finds a vertex given its name in the vertices list
    public  Vertex findsVertex( String theName ) {
        // if we are dealing with the root
        if ( theName==null )
            return null;
          return ( Vertex ) verticesMap.get( theName );
    }
      // inherited constructors


   Graph$$UndirectedCommon (  ) { super(); }
}

//created on: Sat Dec 04 12:37:19 CST 2004

 public class Graph extends  Graph$$UndirectedCommon  {
    // Executes MSTPrim
    public void run( Vertex s )
     {
        Graph gaux = Prim( s );
        Graph.stopProfile();
        gaux.display();
        Graph.resumeProfile();
        super.run( s );
    }
      // inherited constructors


   Graph (  ) { super(); }
}