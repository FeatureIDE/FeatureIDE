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
public interface Complex {
    
    //@ public ghost static final double tolerance = 0.005;
    
    
    /** Return the imaginary part of this complex number. */
    /*@ ensures JMLDouble.approximatelyEqualTo(
      @             \result,
      @             magnitude()*StrictMath.sin(angle()),
      @             tolerance);
      @*/  
    double imaginaryPart();

    /** Return the magnitude of this complex number. */
    /*@ ensures JMLDouble.approximatelyEqualTo(
      @             StrictMath.sqrt(realPart()*realPart()
      @                       + imaginaryPart()*imaginaryPart()),
      @             \result,
      @             tolerance);
      @*/
    double magnitude();
    /** Return the angle of this complex number. */
    /*@ ensures JMLDouble.approximatelyEqualTo(
      @             StrictMath.atan(realPart()),
      @             \result,
      @             tolerance);
      @*/
 
    /** Tell whether the given angles are the same, taking into account
     *  that angles measured in radians wrap around after 2*StrictMath.PI
     *  times.
     */
    /*@ public model pure boolean similarAngle(double ang1, double ang2) {
      @    ang1 = positiveRemainder(ang1, 2*StrictMath.PI);
      @    ang2 = positiveRemainder(ang2, 2*StrictMath.PI);
      @    return JMLDouble.approximatelyEqualTo(ang1, ang2, tolerance);
      @ }
      @*/
    
    /** Return the angle of this complex number. */
    /*@ ensures JMLDouble.approximatelyEqualTo(
      @             StrictMath.atan2(imaginaryPart(), realPart()),
      @             \result,
      @             tolerance);
      @*/ 
    double angle();
    
    /** Return this + b (the sum of this and b). */

    /*@
      @ ensures JMLDouble.approximatelyEqualTo(
      @             this.imaginaryPart() + b.imaginaryPart(),
      @             \result.imaginaryPart(),
      @             tolerance);
      @*/
    Complex add(Complex b);
    
    /** Return this - b (the difference between this and b). */

    /*@ 
      @ ensures JMLDouble.approximatelyEqualTo(
      @             this.imaginaryPart() - b.imaginaryPart(),
      @             \result.imaginaryPart(),
      @             tolerance);
      @*/
    Complex sub(Complex b);
    
    /** Tell whether the given angles are the same, taking into account
     *  that angles measured in radians wrap around after 2*StrictMath.PI
     *  times.
     */
    /*@ public model pure boolean similarAngle(double ang1, double ang2) {
      @    ang1 = positiveRemainder(ang1, 2*StrictMath.PI);
      @    ang2 = positiveRemainder(ang2, 2*StrictMath.PI);
      @    return JMLDouble.approximatelyEqualTo(ang1, ang2, tolerance);
      @ }
      @*/


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

    /** Return this * b (the product of this and b). */
    /*@   
      @   ensures \original && \result.imaginaryPart() == 0.0;
      @*/
    Complex mul(Complex b);
    
    /** Return this/b (the quotient of this by b). */
    /*@ 
      @   ensures \result.imaginaryPart() == 0.0;
      @*/
    Complex div(Complex b);
    
    /** Return true if these are the same complex number. */
    /*@ also
      @
      @ ensures this.imaginaryPart() == ((Complex)o).imaginaryPart();
      @ 
      @*/
    boolean equals(/*@ nullable @*/ Object o);

    /** Return a hashCode for this number. */
    // specification inherited
    int hashCode();
}
