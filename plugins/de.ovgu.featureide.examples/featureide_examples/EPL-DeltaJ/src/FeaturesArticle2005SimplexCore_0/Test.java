package FeaturesArticle2005SimplexCore_0;

import java.math.*;
import java.util.concurrent.locks.Lock;
import java.util.*;

public class Test {

	public Lit f;

	public Lit e;

	public Lit a;


	public void run() {
		___run1();
		System.out.println(this.f.eval());		 
	}

	public void ___run1() {
		___run2();
		System.out.println(this.e.eval());		 
	}

	public void ___run2() {
		___run3();
		this.f = new Neg(this.a,0);
		this.f.print();
		System.out.println("");		 
	}

	public void ___run3() {
		___run4();
		this.e = new Add(this.a,this.a,0);
		this.e.print();
		System.out.println("");		 
	}

	public void ___run4() {
		___run5();
		System.out.println(this.a.eval());		 
	}

	public void ___run5() {
		this.a = new Lit(0);
		this.a.print();
		System.out.println(this.a.value);		 
	}

}
