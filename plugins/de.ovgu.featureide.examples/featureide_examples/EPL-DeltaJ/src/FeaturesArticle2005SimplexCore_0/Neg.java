package FeaturesArticle2005SimplexCore_0;

import java.math.*;
import java.util.concurrent.locks.Lock;
import java.util.*;

public class Neg extends Lit {

	public Lit expr;

	Neg( Lit a ,  int c ) { 
		super(c);
		this.expr = a;
	}


	public int eval() {
		return -1 * (this.expr.eval());
	}

	public void print() {
		System.out.print("-(");
		this.expr.print();
		System.out.print(")");		 
	}

}
