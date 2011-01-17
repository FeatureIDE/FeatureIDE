package FeaturesArticle2005SimplexCore_0;

import java.math.*;
import java.util.concurrent.locks.Lock;
import java.util.*;

public class Add extends Lit {

	public Lit expr1;

	public Lit expr2;

	Add( Lit a ,  Lit b ,  int c ) { 
		super(c);
		this.expr1 = a;
		this.expr2 = b;
	}


	public int eval() {
		return this.expr1.eval() + this.expr2.eval();
	}

	public void print() {
		this.expr1.print();
		System.out.print(" + ");
		this.expr2.print();
		new Integer(1).toString();		 
	}

}
