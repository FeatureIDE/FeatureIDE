























public /*@pure@*/    interface  Complex {
	/*@ 
    
     
    
     ensures JMLDouble.approximatelyEqualTo(
                 magnitude()*StrictMath.cos(angle()),
                 \result,
                 tolerance); @*/
	
        
    double realPart();

	/*@ 
      

    
       requires_redundantly b != null; 
       requires !Double.isNaN(this.magnitude() * b.magnitude());
       requires !Double.isNaN(this.angle()) && !Double.isNaN(b.angle());
       ensures_redundantly \result != null;
       ensures JMLDouble.approximatelyEqualTo(
                   this.magnitude() * b.magnitude(),
                   \result.magnitude(),
                   tolerance);
       ensures similarAngle(this.angle() + b.angle(),
                            \result.angle());
     also
       requires_redundantly b != null;
       requires Double.isNaN(this.magnitude() * b.magnitude())
             || Double.isNaN(this.angle()) || Double.isNaN(b.angle());
       ensures Double.isNaN(\result.realPart());
       ensures \result.imaginaryPart() == 0.0; @*/
	
      
    Complex mul  (Complex b);

	/*@ 

    
     ensures JMLDouble.approximatelyEqualTo(
                 StrictMath.sqrt(realPart()*realPart()
                           + imaginaryPart()*imaginaryPart()),
                 \result,
                 tolerance); @*/
	
      
    double magnitude  ();

	/*@ 
    
  
    
    
    //@ requires_redundantly b != null; 
    //@ ensures_redundantly \result != null;
     ensures JMLDouble.approximatelyEqualTo(
                 this.realPart() + b.realPart(),
                 \result.realPart(),
                 tolerance);
     ensures JMLDouble.approximatelyEqualTo(
                 this.imaginaryPart() + b.imaginaryPart(),
                 \result.imaginaryPart(),
                 tolerance); @*/
	
      
    Complex add  (Complex b);

	/*@ 
    
    
    //@ requires_redundantly b != null; 
    //@ ensures_redundantly \result != null;
     ensures JMLDouble.approximatelyEqualTo(
                 this.realPart() - b.realPart(),
                 \result.realPart(),
                 tolerance);
     ensures JMLDouble.approximatelyEqualTo(
                 this.imaginaryPart() - b.imaginaryPart(),
                 \result.imaginaryPart(),
                 tolerance); @*/
	
      
    Complex sub  (Complex b);

	/*@ 
      


    
     requires d > 0.0;
     ensures \result >= 0.0; @*/
	
     /*@public model pure double positiveRemainder  (double n, double d) {
        n = n % d;
        if (n < 0) {
           n += d;
        }
        return n;
     }@*/

	/*@ 
    
    
       requires_redundantly b != null;
       requires !Double.isNaN(this.magnitude() / b.magnitude());
       requires !Double.isNaN(this.angle()) && !Double.isNaN(b.angle());
       ensures_redundantly \result != null;
       ensures JMLDouble.approximatelyEqualTo(
                   this.magnitude() / b.magnitude(),
                   \result.magnitude(),
                   tolerance);
       ensures similarAngle(this.angle() - b.angle(),
                            \result.angle());
     also
       requires_redundantly b != null;
       requires Double.isNaN(this.magnitude() / b.magnitude())
             || Double.isNaN(this.angle()) || Double.isNaN(b.angle());
       ensures Double.isNaN(\result.realPart());
       ensures \result.imaginaryPart() == 0.0; @*/
	
      
    Complex div  (Complex b);

	/*@ 
    
    
     also @*/ /*@ 
     ensures \result
         <==> o instanceof Complex
              && this.realPart() == ((Complex)o).realPart()
              && this.imaginaryPart() == ((Complex)o).imaginaryPart();
     ensures \result 
         <==> o instanceof Complex
              && this.magnitude() == ((Complex)o).magnitude()
              && this.angle() == ((Complex)o).angle(); @*/
	
      
    boolean equals  ( /*@nullable@*/  Object o);


	
      
    
    
    
    int hashCode  ();

	/*@ 
    
    //@ public ghost static final double tolerance = 0.005;
    
    
    
     ensures JMLDouble.approximatelyEqualTo(
                 \result,
                 magnitude()*StrictMath.sin(angle()),
                 tolerance); @*/
	
        
    double imaginaryPart();


	
    
    
     /*@public model pure boolean similarAngle(double ang1, double ang2) {
        ang1 = positiveRemainder(ang1, 2*StrictMath.PI);
        ang2 = positiveRemainder(ang2, 2*StrictMath.PI);
        return JMLDouble.approximatelyEqualTo(ang1, ang2, tolerance);
     }@*/

	/*@ 
    
     ensures JMLDouble.approximatelyEqualTo(
                 StrictMath.atan(realPart()),
                 \result,
                 tolerance); @*/
	
      
    double angle();


	
    
    
     /*@public model pure boolean similarAngle(double ang1, double ang2) {
        ang1 = positiveRemainder(ang1, 2*StrictMath.PI);
        ang2 = positiveRemainder(ang2, 2*StrictMath.PI);
        return JMLDouble.approximatelyEqualTo(ang1, ang2, tolerance);
     }@*/


}
