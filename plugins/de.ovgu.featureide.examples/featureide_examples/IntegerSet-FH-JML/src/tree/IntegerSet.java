//@ model import org.jmlspecs.models.*;


public   class  IntegerSet {
	
    //@ public model instance JMLValueSet theSet;
	//@ public instance invariant_redundantly theSet != null;
	//@ public initially theSet.isEmpty();
	//@ public instance invariant
	//@       (\forall JMLType e; theSet.has(e);
	//@                           e instanceof JMLInteger);
     
	public  int dummy;

	/*@ 

    
     public normal_behavior
       assignable theSet;
       ensures theSet.equals(\old(theSet.insert(new JMLInteger(elem))));
	@*/ 

    
    public void insert(int elem) {
        if (isEmpty) {
            isEmpty = false;
            rootValue = elem;
        } else if (rootValue != elem) {
            if (elem < rootValue) {
                if (left == null) {
                    left = new IntegerSet(elem, this);
                } else {
                    left.insert(elem);
                }
            } else {
                //@ assume rootValue < elem;
                if (right == null) {
                    right = new IntegerSet(elem, this);
                } else {
                    right.insert(elem);
                }
            }
        }
    }

	/*@ 

    
     public normal_behavior	
       ensures \result == theSet.has(new JMLInteger(elem));
	@*/ 

    
    public  /*@pure@*/ 
	boolean isMember(int elem) {
        if (isEmpty) {
            return false;
        } else if (rootValue == elem) {
            return true;
        } else if (elem < rootValue) {
            if (left == null) {
                return false;
            } else {
                return left.isMember(elem);
            }
        } else {
            //@ assume rootValue < elem;
            if (right == null) {
                return false;
            } else {
                return right.isMember(elem);
            }
        }
    }

	/*@  

    
     public normal_behavior
       assignable theSet;
       ensures theSet.equals( \old(theSet.remove(new JMLInteger(elem))) );
	@*/ 

    
    public void remove  (int elem) {
        removeHelper(elem);
    }

	

    
    private  boolean isEmpty;

	
    //@                 in theSet;
    
    private  int rootValue;

	
    //@                 in theSet;
    
    private  /*@nullable@*/    IntegerSet left;

	
    //@                         in theSet;
    //@                         maps left.theSet \into theSet;
    
    private  /*@nullable@*/    IntegerSet right;

	
    //@                          in theSet;
    //@                          maps right.theSet \into theSet;
    
    private  /*@nullable@*/    IntegerSet parent;

	/*@ 
    //@                          in theSet;

    //@  private represents theSet <- abstractValue();

     private  invariant  (left != null || right != null) ==> !isEmpty @*/

	/*@  
     
     private  invariant  left != null ==>
                (\forall JMLInteger i; i != null && left.theSet.has(i);
                                       i.intValue() < rootValue) @*/

	/*@ 
     private  invariant  right != null ==>
                (\forall JMLInteger i; i != null && right.theSet.has(i);
                                       rootValue < i.intValue()) @*/

	/*@ 
     
     private  invariant  parent != null ==> !parent.isEmpty @*/

	/*@ 
     private  invariant  parent != null && parent.left != null
                       ==> parent.left.rootValue < parent.rootValue @*/

	/*@  
     private  invariant  parent != null && parent.right != null
                       ==> parent.rootValue < parent.right.rootValue @*/

	/*@ 
      

     private  invariant  left != null
                        ==> !left.isEmpty && left.rootValue < rootValue @*/

	/*@ 
      private  invariant  right != null
                        ==> !right.isEmpty && rootValue < right.rootValue @*/

	/*@ 
      

    
     public normal_behavior
       assignable theSet;
       ensures theSet.isEmpty();
	@*/ 
      
    public IntegerSet() {
        isEmpty = true;
        parent = null;
        constrHelper();
    }

	/*@ 

     protected normal_behavior
       assignable theSet;
       ensures theSet.equals(new JMLValueSet(new JMLInteger(elem)));
	@*/  
      
    protected IntegerSet(int elem, IntegerSet par) {
        isEmpty = false;
        rootValue = elem;
        parent = par;
        constrHelper();
    }

	

    
    //@ private normal_behavior
    //@   assignable theSet;
    //@   ensures left == null && right == null;
    //@   ensures \not_modified(isEmpty) && \not_modified(parent);
    //@   ensures \not_modified(rootValue);
    private  /*@helper@*/  void constrHelper() {
        right = null;
        left = null;
    }

	/*@ 

    
     private normal_behavior
       assignable theSet;
       ensures theSet.equals( \old(theSet.remove(new JMLInteger(elem))) );
	@*/ 
      
    private  /*@helper@*/  void removeHelper(int elem) {
        if (!isEmpty) {
            if (rootValue == elem) {
                if (left == null && right == null) {
                    removeLeaf();
                } else {
                    removeRoot();
                }
            } else if (elem < rootValue) {
                if (left != null) {
                    left.removeHelper(elem);
                }
            } else {
                //@ assume rootValue < elem;
                if (right != null) {
                    right.removeHelper(elem);
                }
            }
        }
    }

	

    
    //@ requires left != null || right != null;
    //@ assignable theSet;
    private  /*@helper@*/  void removeRoot() {
        IntegerSet next = getSuccessor(); 
        if (next == null) {                 
            next = getPredecessor();            
            //@ assume next != null;
            rootValue = next.rootValue; 
            left.removeHelper(rootValue);
        } else { 
            //@ assume next != null;
            rootValue = next.rootValue;
            right.removeHelper(rootValue);
        }
    }

	/*@ 

    
     requires left == null && right == null;
     {|
        requires parent != null;
        assignable parent.theSet, isEmpty;
      also
        requires parent == null;
        assignable isEmpty;
     |}
	@*/ 
      
    private  /*@helper@*/  void removeLeaf() {
        if (parent != null) {
            if (isLeftChild()) {
                parent.left = null;
            } else {
                parent.right = null;
            }
        }
        
        isEmpty = true;
    }

	

    
    //@ requires parent != null;
    private  /*@helper@*/ /*@pure@*/  boolean isLeftChild() {
        return parent.left == this;
    }

	/*@ 

     requires right == null;
      ensures \result == null;
     also
      requires right != null;
      ensures \result != null
              && \result.theSet.has(new JMLInteger(
                    (\min int i; right.theSet.has(new JMLInteger(i)); i)));
	@*/ 
      
    private  /*@helper@*/ /*@pure@*/ /*@nullable@*/  IntegerSet getSuccessor() {
        IntegerSet tree = right;
        if (right != null) {
            while (tree.left != null) {
                tree = tree.left;
            }
            //@ assert tree.left == null;
        }
        return tree;
    }

	/*@ 

     requires left == null;
      ensures \result == null;
     also
      requires left != null;
      ensures \result != null
              && \result.theSet.has(new JMLInteger(
                    (\max int i; left.theSet.has(new JMLInteger(i)); i)));
	@*/ 
      
    private  /*@helper@*/ /*@pure@*/ /*@nullable@*/  IntegerSet getPredecessor() {
        IntegerSet tree = left;
        if (left != null) {
            while (tree.right != null) {
                tree = tree.right;
            }
            //@ assert tree.right == null;
        }
        return tree;
    }

	

    
    public  /*@pure@*/  String toString() {
        return "{" + this.printTree(true) + "}";
    }

	/*@ 

     protected normal_behavior
       assignable \nothing;
       ensures \result != null;
	@*/ 
      
    protected  /*@pure@*/  String printTree(boolean isFirst) {
        String ans = "";

        if (!isEmpty) {
            if (left != null) {
                ans += left.printTree(isFirst);
                if (!left.isEmpty) {
                    isFirst = false;
                }
            }
            if (!isFirst) {
                ans += ", ";
            }
            ans += Integer.toString(rootValue);
            if (right != null) {
                ans += right.printTree(false);
            }
        }
		
        return ans;
    }

	/*@ 

    
    
      ensures \result != null;
	@*/ 
      /*@public model pure JMLValueSet abstractValue()
      {
          JMLValueSet ret = new JMLValueSet();
          if (!isEmpty) { 
              if (left != null) {
                  ret = ret.union(left.abstractValue());
              }
              ret = ret.insert(new JMLInteger(rootValue));
              if (right != null) {
                  ret = ret.union(right.abstractValue());
              }
          }
          return ret;
      }@*/


}
