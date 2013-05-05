

















import java.util.*; 

















import java.awt.Color; 


public /*@nullable_by_default@*/   class  Digraph {
	/*@ 

	//@ public model JMLValueSet nodes;
	//@ public model JMLValueSet arcs;

	 public  invariant_redundantly nodes != null; @*/

	/*@ 
	  public  invariant (\forall JMLType n; nodes.has(n);
	                           n instanceof NodeType); @*/

	/*@ 
	  public  invariant_redundantly arcs != null; @*/

	/*@ 
	  public  invariant (\forall JMLType a; arcs.has(a);
	                           a instanceof ArcType); @*/

	/*@  
	  public  invariant
	       (\forall ArcType a; arcs.has(a);
	            nodes.has(a.from) && nodes.has(a.to)); @*/

	
	   
	 
    protected  /*@spec_public@*/  HashSet nodeSet;

	
    //@                           in nodes;
    //@                           maps nodeSet.theSet \into nodes;
    protected  /*@spec_public@*/  HashSet arcSet;

	/*@ 
    //@                           in arcs;
    //@                           maps arcSet.theSet \into arcs;

    //@ private represents nodes <- JMLValueSet.convertFrom(nodeSet);
    //@ private represents arcs <- arcAbstractValue(arcSet);

     private  invariant_redundantly nodeSet != null; @*/

	/*@ 
     private  invariant (\forall Object e; nodeSet.contains(e); 
                           e!=null && e instanceof NodeType); @*/

	/*@ 
     
     private  invariant_redundantly arcSet != null; @*/

	/*@ 
     private  invariant (\forall Object e; arcSet.contains(e); 
                           e!=null && e instanceof Arc); @*/

	/*@ 
      

	   public normal_behavior
	    assignable nodes, arcs;
	    ensures nodes.isEmpty() && arcs.isEmpty(); @*/
	
	   
    public Digraph() {
        nodeSet = new HashSet();
        arcSet = new HashSet();
    }

	/*@ 

	   public normal_behavior
	    requires_redundantly n != null;
	    assignable nodes;
	    ensures nodes.equals(\old(nodes.insert(n))); @*/
	
	   
    public void addNode(NodeType n) {
        nodeSet.add(n);
    }

	/*@ 

	   public normal_behavior
	    requires_redundantly inFrom != null && inTo != null;
	    requires nodes.has(inFrom) && nodes.has(inTo);
	    assignable arcs;
	    ensures arcs.equals(
	             \old(arcs).insert(new ArcType(inFrom, inTo))); @*/
	
	   
    public void addArc(NodeType inFrom, NodeType inTo) {
        arcSet.add(new Arc(inFrom, inTo));
    }

	/*@ 

	  public normal_behavior
	   assignable \nothing;
	   ensures \result == nodes.has(n);
     also 
      public normal_behavior
        ensures \result == nodeSet.contains(n); @*/
	
      
    public /*@pure@*/ boolean isNode(NodeType n) {
        return nodeSet.contains(n);
    }

	/*@ 

	   public normal_behavior
	    requires_redundantly inFrom != null && inTo != null;
	    ensures \result == arcs.has(new ArcType(inFrom, inTo)); @*/
	
	  	   
    public /*@pure@*/ boolean isArc(NodeType inFrom, NodeType inTo) {
        return arcSet.contains(new Arc(inFrom, inTo));
    }

	/*@ 

	   public normal_behavior
	    requires nodes.has(start) && nodes.has(end);
	    assignable \nothing;
	    ensures \result
	            == reachSet(new JMLValueSet(start)).has(end); @*/
	
	   
    public /*@pure@*/ boolean isAPath(NodeType start, NodeType end) {
        return reachSet(start).contains(end);
    }


	

    protected /*@pure@*/ HashSet reachSet(NodeType start) {
        HashSet disc = new HashSet(); 
        Iterator arcs = arcSet.iterator();
        while (arcs.hasNext()) {
            Arc next = (Arc) arcs.next();
            if (next.getSource() == start && !disc.contains(next.getTarget())) {
                disc.add(next.getTarget());
                reachSet(next.getTarget());
            }
        }

        return disc;
    }


	
  
     /*@private pure model JMLValueSet arcAbstractValue(HashSet arcs) {
       JMLValueSet ret = new JMLValueSet();
       Iterator arcIter = arcs.iterator();
       while (arcIter.hasNext()) {
         Arc a = (Arc) arcIter.next();
         NodeType from = a.getSource();
         NodeType to = a.getTarget();
         ret = ret.insert(new ArcType(from, to));
       }
       return ret;
     }@*/


	
      

    public String toString() {
        return "[arcs: " + arcSet.toString()
               + "\n nodes: " + nodeSet.toString() + "]";
    }

	/*@ 

	   public normal_behavior
	    assignable \nothing;
	    ensures \result <==>
	               !(\exists ArcType a; arcs.has(a);
	                      a.from.equals(n) || a.to.equals(n)); @*/
	
	   
    public /*@pure@*/ boolean unconnected(NodeType n) {
        Iterator arcIter = arcSet.iterator();
        while (arcIter.hasNext()) {
            Arc a = (Arc) arcIter.next();
            if (a.getSource().equals(n) || a.getTarget().equals(n)) {
                return false;
            }
        }
        return true;
    }

	/*@ 

    
     public normal_behavior
      assignable arcs;
      ensures nodes.equals(\old(nodes));
      ensures arcs.equals(flipAll(\old(arcs))); @*/
	
      
    public void transpose() {
        Iterator arciter = arcSet.iterator();
        while (arciter.hasNext()) {
            Arc a = (Arc) arciter.next();
            a.flip();
        }
    }


	

    
      /*@public model pure JMLValueSet flipAll(JMLValueSet s)
     {
         JMLValueSet ret = new JMLValueSet();
         JMLIterator iter = s.iterator();
         while (iter.hasNext()) {
           ArcType a = (ArcType) iter.next();
           ret = ret.insert(new ArcType(a.to, a.from));
         }
         return ret;
       }@*/

	

    private /*@spec_public@*/ int time;

	/*@  

    

     public normal_behavior
      assignable time, arcs, nodes; @*/
	
      
    public void DFS() {
        Iterator nodes = nodeSet.iterator();
        while (nodes.hasNext()) {
            SearchableNode next = (SearchableNode) nodes.next();
            next.setColor(Color.WHITE);
            next.setPredecessor(null);
        }
        time = 0;
        while (nodes.hasNext()) {
            SearchableNode next = (SearchableNode) nodes.next();
            if (next.getColor() == Color.WHITE) {
                DFSVisit(next);
            }
        }
    }

	/*@ 

     public normal_behavior
      requires u != null && u.color != null && u.color == Color.WHITE;
      assignable time, arcs, u.discoverTime, u.color,
                 u.predecessor, u.finishTime;
      ensures u.color == Color.BLACK && u.discoverTime == \old(time + 1)
           && time > \old(time); @*/
	 
      
    public void DFSVisit(SearchableNode u) {
        u.setColor(Color.GRAY);
        time++;
        u.setDiscoverTime(time);
        Iterator arcs = arcSet.iterator();
        while (arcs.hasNext()) {
            Arc next = (Arc) arcs.next();
            if (next.getSource() == u) {
                if (((SearchableNode) next.getTarget()).getColor()
                    == Color.WHITE) {
                        ((SearchableNode) next.getTarget())
                            .setPredecessor((SearchableNode) next.getSource());
                    DFSVisit((SearchableNode) next.getTarget());
                }
            }
        }
        u.setColor(Color.BLACK);
        u.setFinishTime(time);
        time++;
    }

	/*@ 

	   public normal_behavior
	    requires unconnected(n);
	    assignable nodes;
	    ensures nodes.equals(\old(nodes.remove(n))); @*/
	
	   
    public void removeNode(NodeType n) {
        nodeSet.remove(n);
    }

	/*@ 

	   public normal_behavior
	    requires_redundantly inFrom != null && inTo != null;
	    requires nodes.has(inFrom) && nodes.has(inTo);
	    assignable arcs;
	    ensures arcs.equals(
	             \old(arcs).remove(new ArcType(inFrom, inTo))); @*/
	
	   
    public void removeArc(NodeType inFrom, NodeType inTo) {
        arcSet.remove(new Arc(inFrom, inTo));
    }


}
