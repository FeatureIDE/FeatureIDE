// @(#)$Id: Complex.java 1199 2009-02-17 19:42:32Z smshaner $

// Copyright (C) 2003 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.




/** Complex numbers.  Note that these are immutable.
 * Abstractly, one can think of a complex number as
 *  realPart+(imaginaryPart*i).
 * Alternatively, one can think of it as distance
 * from the origin along a given angle 
 * (measured in radians counterclockwise from
 * the positive x axis), hence a pair of
 *  (magnitude, angle).
 * This class supports both of these views.
 *
 * The specifications in this class are intentionally of the lightweight
 * variety.
 *
 * @author Gary T. Leavens with help from Abelson and Sussman's
 *          <cite>Structure and Interpretation of Computer Programs</cite>
 */
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
      @ also
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
      @   ensures \result.imaginaryPart() == 0.0;
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
