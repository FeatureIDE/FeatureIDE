//layer Weighted;

using System.Collections;

// of Graph
 
// The weighted layer needs to extend Vertex to provide a new 
// ArrayList to hold the  weigths  of the edges
// ************************************************************

public class Vertex {//refines
    public ArrayList weightsList;
 
    public void VertexConstructor() {
        original();
        weightsList = new ArrayList();
    }
         
    public void AddWeight( int weight )
    {
        weightsList.Add(weight ) ;
    }
    
    public void adjustAdorns( Vertex the_vertex, int index )
    {
        int the_weight = (int)(the_vertex.weightsList[index] );
        weightsList.Add(the_weight );
        original( the_vertex, index );
    }
                          
    public void display()
    {
        int s = weightsList.Count;
        int i;

        System.Console.Out.Write( " Weights : " );

        for ( i=0; i<s; i++ ) {
            System.Console.Out.Write( (weightsList[i] + ", " )); // ALEX INTEGER
        }

        original();
    }

}
