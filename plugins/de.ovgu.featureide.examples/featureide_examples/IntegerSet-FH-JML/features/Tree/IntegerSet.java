//@ model import org.jmlspecs.models.*;

/** Sets of integers implemented as binary search trees.
 *  This implementation demonstrates the use of JML's helper modifier.
 * @author Katie Becker
 * @author Gary T. Leavens
 * @author Arthur Thomas
 */
public class IntegerSet {

    /** Is this tree empty?  When this is true, rootValue is not defined. */
    private boolean isEmpty;
    //@                 in theSet;
    /** The integer at the root of the set. */
    private int rootValue;
    //@                 in theSet;
    /** The left subtree, which may be null. */
    private /*@ nullable @*/ IntegerSet left;
    //@                         in theSet;
    //@                         maps left.theSet \into theSet;
    /** The right subtree, which may be null. */
    private /*@ nullable @*/ IntegerSet right;
    //@                          in theSet;
    //@                          maps right.theSet \into theSet;
    /** The parent of this subtree, which may be null. */
    private /*@ nullable @*/ IntegerSet parent;
    //@                          in theSet;

    //@  private represents theSet <- abstractValue();

    /*@ private invariant (left != null || right != null) ==> !isEmpty; 
      @
      @ private invariant left != null ==>
      @            (\forall JMLInteger i; i != null && left.theSet.has(i);
      @                                   i.intValue() < rootValue);
      @ private invariant right != null ==>
      @            (\forall JMLInteger i; i != null && right.theSet.has(i);
      @                                   rootValue < i.intValue());
      @
      @ private invariant parent != null ==> !parent.isEmpty;
      @ private invariant parent != null && parent.left != null
      @                   ==> parent.left.rootValue < parent.rootValue; 
      @ private invariant parent != null && parent.right != null
      @                   ==> parent.rootValue < parent.right.rootValue;
      @*/

    /*@ private invariant left != null
      @                    ==> !left.isEmpty && left.rootValue < rootValue;
      @  private invariant right != null
      @                    ==> !right.isEmpty && rootValue < right.rootValue;
      @*/

    /** Initialize this integer set to be empty. */
    /*@ public normal_behavior
      @   assignable theSet;
      @   ensures theSet.isEmpty();
      @*/
    public IntegerSet() {
        isEmpty = true;
        parent = null;
        constrHelper();
    }

    /*@ protected normal_behavior
      @   assignable theSet;
      @   ensures theSet.equals(new JMLValueSet(new JMLInteger(elem))); 
      @*/
    protected IntegerSet(int elem, IntegerSet par) {
        isEmpty = false;
        rootValue = elem;
        parent = par;
        constrHelper();
    }

    /** Set the left and right to null. */
    //@ private normal_behavior
    //@   assignable theSet;
    //@   ensures left == null && right == null;
    //@   ensures \not_modified(isEmpty) && \not_modified(parent);
    //@   ensures \not_modified(rootValue);
    private /*@ helper @*/ void constrHelper() {
        right = null;
        left = null;
    }

    // specification inherited
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

    // specification is inherited
    public /*@ pure @*/
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

    // specification is inherited
    public void remove(int elem) {
        removeHelper(elem);
    }

    /** Remove the given integer from this set.  Note that the
     *  invariants don't all apply to this method.  That is important,
     *  because the tree surgery done by this method calls this method
     *  recursively in states in which the invariant does not hold.
     */
    /*@ private normal_behavior
      @   assignable theSet;
      @   ensures theSet.equals( \old(theSet.remove(new JMLInteger(elem))) );
      @*/
    private /*@ helper @*/ void removeHelper(int elem) {
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

    /** Replace the current node with the successor or predecessor. */
    //@ requires left != null || right != null;
    //@ assignable theSet;
    private /*@ helper @*/ void removeRoot() {
        IntegerSet next = getSuccessor(); 
        if (next == null) {                 
            next = getPredecessor();            
            //@ assume next != null;
            rootValue = next.rootValue; // left subtree
            left.removeHelper(rootValue);
        } else { // right subtree
            //@ assume next != null;
            rootValue = next.rootValue;
            right.removeHelper(rootValue);
        }
    }

    /** Remove an integer from a leaf node. */
    /*@ requires left == null && right == null;
      @ {|
      @    requires parent != null;
      @    assignable parent.theSet, isEmpty;
      @  also
      @    requires parent == null;
      @    assignable isEmpty;
      @ |}
      @*/
    private /*@ helper @*/ void removeLeaf() {
        if (parent != null) {
            if (isLeftChild()) {
                parent.left = null;
            } else {
                parent.right = null;
            }
        }
        // empty this node
        isEmpty = true;
    }

    /** Is this node and left child of its parent?. */
    //@ requires parent != null;
    private /*@ helper pure @*/ boolean isLeftChild() {
        return parent.left == this;
    }

    /*@ requires right == null;
      @  ensures \result == null;
      @ also
      @  requires right != null;
      @  ensures \result != null
      @          && \result.theSet.has(new JMLInteger(
      @                (\min int i; right.theSet.has(new JMLInteger(i)); i)));
      @*/
    private /*@ helper pure nullable @*/ IntegerSet getSuccessor() {
        IntegerSet tree = right;
        if (right != null) {
            while (tree.left != null) {
                tree = tree.left;
            }
            //@ assert tree.left == null;
        }
        return tree;
    }

    /*@ requires left == null;
      @  ensures \result == null;
      @ also
      @  requires left != null;
      @  ensures \result != null
      @          && \result.theSet.has(new JMLInteger(
      @                (\max int i; left.theSet.has(new JMLInteger(i)); i)));
      @*/
    private /*@ helper pure nullable @*/ IntegerSet getPredecessor() {
        IntegerSet tree = left;
        if (left != null) {
            while (tree.right != null) {
                tree = tree.right;
            }
            //@ assert tree.right == null;
        }
        return tree;
    }

    // specification is inherited
    public /*@ pure @*/ String toString() {
        return "{" + this.printTree(true) + "}";
    }

    /*@ protected normal_behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @*/
    protected /*@ pure @*/ String printTree(boolean isFirst) {
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

    /** Return the abstract value of this IntegerSet. */
    /*@
      @  ensures \result != null;
      public model pure JMLValueSet abstractValue()
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
      }  @*/

}