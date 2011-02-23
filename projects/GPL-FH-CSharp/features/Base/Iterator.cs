using System.Collections.Generic;
public class Iterator<RT, ET> : Iterator<RT> {
        public new delegate RT Transformer(ET val);
        Transformer trans;
        IEnumerator<ET> e;
        //ET = Enumerator Type
        //RT = Type that is returned by this Iterator
        public Iterator(IEnumerator<ET> e, Transformer transformer) 
            : base () {
            this.e = e;
            trans = transformer;
        }
        public override RT next() {
            if (!moved) {
                e.MoveNext();
            }
            moved = false;
            return trans(e.Current);
        }
        public override bool hasNext() {
            if (!moved) {
                moved = true;
                lastMoveResult = e.MoveNext();
                return lastMoveResult;
            }
            else {
                return lastMoveResult;
            }
        }

    }
public class Iterator<RT> {
    public delegate RT Transformer(RT val);
    protected bool moved = false;
    protected bool lastMoveResult;
    IEnumerator<RT> e;
    Transformer trans;
    /*
     * Bei der Rückgabe des nächsten elements (next() funktion) wird transformer auf dieses Objekt angewandt.
     */
    public Iterator(IEnumerator<RT> e, Transformer transformer) {
        this.e = e;
        trans = transformer;
    }
    protected Iterator() {
    }
    public Iterator(IEnumerator<RT> e) {
        this.e = e;
        trans = NotTransform;
    }
    public static RT NotTransform(RT val) {
        return val;
    }
    public virtual RT next() {
        if (!moved) {
            e.MoveNext();
        }
        moved = false;
        return trans(e.Current);
    }
    public virtual bool hasNext() {
        if (!moved) {
            moved = true;
            lastMoveResult = e.MoveNext();
            return lastMoveResult;
        }
        else {
            return lastMoveResult;
        }
    }
}

