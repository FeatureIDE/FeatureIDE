
public /*@ pure @*/ interface Complex {
    
     
    /** Return the real part of this complex number. */
    /*@ ensures JMLDouble.approximatelyEqualTo(
      @             magnitude()*StrictMath.cos(angle()),
      @             \result,
      @             tolerance);
      @*/  
    double realPart();
    
    /** Return this * b (the product of this and b). */
    /*@   requires_redundantly b != null; 
      @   requires !Double.isNaN(this.magnitude() * b.magnitude());
      @   requires !Double.isNaN(this.angle()) && !Double.isNaN(b.angle());
      @   ensures_redundantly \result != null;
      @   ensures JMLDouble.approximatelyEqualTo(
      @               this.magnitude() * b.magnitude(),
      @               \result.magnitude(),
      @               tolerance);
      @   ensures similarAngle(this.angle() + b.angle(),
      @                        \result.angle());
      @   also
      @   requires_redundantly b != null;
      @   requires Double.isNaN(this.magnitude() * b.magnitude())
      @         || Double.isNaN(this.angle()) || Double.isNaN(b.angle());
      @   ensures Double.isNaN(\result.realPart());
      @  
      @*/
    Complex mul(Complex b);

    /** Return the magnitude of this complex number. */
    /*@ ensures JMLDouble.approximatelyEqualTo(
      @             StrictMath.abs(realPart()),
      @             \result,
      @             tolerance);
      @*/
    double magnitude();
    

    
    /** Return this + b (the sum of this and b). */
    //@ requires_redundantly b != null; 
    //@ ensures_redundantly \result != null;
    /*@ ensures JMLDouble.approximatelyEqualTo(
      @             this.realPart() + b.realPart(),
      @             \result.realPart(),
      @             tolerance);
      @*/
    Complex add(Complex b);
    
    /** Return this - b (the difference between this and b). */
    //@ requires_redundantly b != null; 
    //@ ensures_redundantly \result != null;
    /*@ ensures JMLDouble.approximatelyEqualTo(
      @             this.realPart() - b.realPart(),
      @             \result.realPart(),
      @             tolerance);
      @*/
    Complex sub(Complex b);
    



    
    /** Return the positive remainder of n divided by d. */
    /*@ requires d > 0.0;
      @ ensures \result >= 0.0;
      @ public model pure double positiveRemainder(double n, double d) {
      @    n = n % d;
      @    if (n < 0) {
      @       n += d;
      @    }
      @    return n;
      @ }
      @*/


    
    /** Return this/b (the quotient of this by b). */
    /*@   requires_redundantly b != null;
      @   requires !Double.isNaN(this.magnitude() / b.magnitude());
      @   requires !Double.isNaN(this.angle()) && !Double.isNaN(b.angle());
      @   ensures_redundantly \result != null;
      @   ensures JMLDouble.approximatelyEqualTo(
      @               this.magnitude() / b.magnitude(),
      @               \result.magnitude(),
      @               tolerance);
      @   ensures similarAngle(this.angle() - b.angle(),
      @                        \result.angle());
      @ also
      @   requires_redundantly b != null;
      @   requires Double.isNaN(this.magnitude() / b.magnitude())
      @         || Double.isNaN(this.angle()) || Double.isNaN(b.angle());
      @   ensures Double.isNaN(\result.realPart());
      @*/
    Complex div(Complex b);
    
    /** Return true if these are the same complex number. */
    /*@ also
      @ ensures \result
      @     <==> o instanceof Complex
      @          && this.realPart() == ((Complex)o).realPart();
      @        
      @ ensures \result 
      @     <==> o instanceof Complex
      @          && this.magnitude() == ((Complex)o).magnitude()
      @          && this.angle() == ((Complex)o).angle();
      @*/
    boolean equals(/*@ nullable @*/ Object o);

    /** Return a hashCode for this number. */
    // specification inherited
    int hashCode();
}
