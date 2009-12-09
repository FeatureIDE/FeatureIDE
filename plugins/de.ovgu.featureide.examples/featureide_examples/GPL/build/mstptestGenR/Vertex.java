package mstptestGenR;



class Vertex {
  public String name = null;

  public  Vertex assignName( String name ) {
      ((Vertex) this).name = name;
      return ( Vertex ) ((Vertex) this);
  }

  public String getName( ) {  return ((Vertex) this).name; }
}