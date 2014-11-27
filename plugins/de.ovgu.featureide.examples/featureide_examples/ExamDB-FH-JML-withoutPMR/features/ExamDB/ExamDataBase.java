/**
 * Abstrakte ExamDataBase Klasse. Speichert Benotungsparameter, Teilnehmerdaten
 * und erm&ouml;glicht Abfragen der Datenbasis.
 */
public abstract class ExamDataBase {

    /**
     * Die maximal erreichbare Punktzahl
     */
    protected /*@spec_public@*/ int maxPoints;

    /**
     * Die Bestehensgrenze. Ist immer echt gr&ouml;&szlig;er <code>null</code>
     * und kleiner oder gleich <code>maxPoints</code>.
     */
    protected /*@spec_public@*/ int threshold;

    /*@ public invariant
      @  0<threshold && threshold<=maxPoints;
      @*/  

    /**
     * Die Schrittweite zwischen den einzelnen Notenstufen. Liegt im Bereich von
     * echt gr&ouml;&szlig;er 0 bis <code>(maxPoints-threshold)/10</code>.
     */
    protected /*@spec_public@*/ int step;

    /*@ public invariant
      @  0<step && step<=(maxPoints-threshold)/10;
      @*/  

    /**
     * Die zu der Klausur angemeldeten Studenten, auch diejenigen, die sich wieder
     * abgemeldet haben. <code>students</code> ist niemals <code>null</code>. 
     * F&uuml;r alle Studenten in <code>students</code> gilt:
     * <ul>
     *   <li> Die Punktzahl jedes Studenten liegt zwischen -1 und <code>maxPoints</code></li>
     *   <li> Jeder Student hat eine eindeutige Matrikelnummer und kommt nur einmal in
     *        <code>students</code> vor.</li>
     *   <li> Jedes Objekt der Klasse <code>Student</code> ist in höchstens einer 
     *        <code>ExamDataBase</code> enthalten. </li>
     *   <li> Die Bonuspunktzahl liegt zwischen 0 und <code>maxPoints</code>.</li>
     * </ul>
     */
    protected /*@spec_public@*/ /*@nullable@*/ Student[] students;

    /*@ public invariant
      @  students!=null
      @  && (\forall int i; 
      @          0<=i && i<students.length && students[i]!=null;
      @              (\forall ExamDataBase ex; ex!=null && ex!=this; (\forall int k;
      @                   0<=k && k<ex.students.length; ex.students[k]!=students[i]))
      @              && -1<=students[i].points 
      @              && students[i].points<=maxPoints 
      @              && (\forall int j; 
      @                       0<=j && j<students.length 
      @                       && students[j]!=null && i!=j; 
      @                           students[i].matrNr!=students[j].matrNr));
      @*/

    /**
     * Berechnet aus Punkt- und Bonuspunktzahl die Note. Noten liegen im Bereich
     * von 100 bis 500 (1,0 bis 5,0).
     */
    /*@ protected normal_behavior
      @  ensures \result==pointsToGrade(points, bonusPoints);
      @*/
    protected /*@spec_public@*/ /*@pure@*/ int pointsToGrade(int points, 
							     int bonusPoints){
        points += (points<threshold 
        	   ? 0 
                   : (bonusPoints<=step 
                      ? bonusPoints 
                      : step));        
	return (points<threshold
                ? 500
                : ((points-threshold)/step>=9 
                   ? 100 
                   : (400 - 100*((points-threshold)/(3*step)) 
                          - (((points-threshold)/step)%3==1
                             ? 30 
                             : ((points-threshold)/step)%3==2 
                                ? 70 
                                : 0))));
    }

    /** 
     * Setzt die Bestehensgrenze (<code>threshold</code>), die Schrittweite (<code>step</code>)
     * und die Maximalpunktzahl (<code>maxPoints</code>)
     * auf die neuen Werte newThreshold, newStep und newMaxPoints, falls diese die folgenden
     * Bedingungen erf&uuml;llen:
     * <ul>
     *   <li> 0&lt;newThreshold</li>
     *   <li> 0&lt;newStep</li>
     *   <li> newStep&lt;=(newMaxPoints-newThreshold)/10</li>
     *   <li> newThreshold&lt;=newMaxPoints </li>
     * </ul>
     * andernfalls wird eine <code>ExamDataBaseException</code> geworfen.
     * @param newThreshold der neue Wert f&uuml;r die Bestehensgrenze <code>threshold</code>
     * @param newStep der neue Wert f&uuml;r die Schrittweite <code>step</code>
     * @param newMaxPoints der neue Wert f&uuml;r die Maximalpunktzahl <code>maxPoints</code>
     * @throws ExamDataBaseException wird geworfen, falls die obigen Konsistenzbedingungen nicht erf&uuml;llt sind.
     */
    /*@ public normal_behavior
      @  requires 0<newThreshold && newThreshold<=newMaxPoints 
      @           && 0<newStep && newStep<=(newMaxPoints-newThreshold)/10;
      @  assignable threshold, step, maxPoints;
      @  ensures threshold==newThreshold 
      @          && step==newStep 
      @          && maxPoints==newMaxPoints;
      @ also public exceptional_behavior
      @  requires !(0<newThreshold && newThreshold<=newMaxPoints 
      @             && 0<newStep && newStep<=(newMaxPoints-newThreshold)/10);

      @  signals_only ExamDataBaseException;
      @*/  
    public abstract void setExamParameters(int newThreshold, 
                                           int newStep, 
                                           int newMaxPoints) 
						throws ExamDataBaseException;

    /**
     * F&uuml;gt einen Studenten mit der Matrikelnummer <code>matrNr</code>, dem
     * Vornamen <code>firstname</code> und dem Nachnamen <code>surname</code>
     * zur Datenbasis hinzu, falls:
     * <ul>
     *   <li> <code>firstname</code> und <code>surname</code> nicht <code>null</code> sind</li>
     *   <li> <code>matrNr</code>&gt;0 gilt.
     *   <li> noch kein Student mit der Matrikelnummer <code>matrNr</code> in der Datenbasis
     *       vorhanden ist</li>
     * </ul> 
     * andernfalls wird eine <code>ExamDataBaseException</code> geworfen.
     * @param matrNr die Matrikelnummer des hinzuzuf&uuml;genden Studenten.
     * @param firstname der Vorname des Studenten.
     * @param surname der Nachname des Studenten.
     * @throws ExamDataBaseException wird geworfen, falls die obigen Konsistenzbedingungen nicht erf&uuml;llt sind. 
     */
    /*@ public normal_behavior
      @  requires matrNr>0 && firstname!=null && surname!=null 
      @           && (\forall int i; 
      @                   0<=i && i<students.length && students[i]!=null;
      @                       students[i].matrNr!=matrNr);
      @  assignable students, students[*];
      @  ensures (\exists int i; 
      @               0<=i && i<students.length && students[i]!=null; 
      @	                  students[i].matrNr==matrNr 
      @                   && students[i].firstname==firstname 
      @                   && students[i].surname==surname 
      @                   && students[i].points==-1);
      @  ensures (\forall int i; 
      @               0<=i && i<students.length && students[i]!=null 
      @               && students[i].matrNr != matrNr;      
      @                   (\exists int j; 
      @                        0<=j && j<\old(students).length;
      @                            \old(students[j])==students[i]));
      @  ensures (\forall int i;
      @              0<=i && i<\old(students).length && \old(students[i])!=null;
      @                  (\exists int j;
      @                       0<=j && j<students.length;
      @                           students[j]==\old(students[i])));
      @ also public exceptional_behavior
      @  requires !(matrNr>0 && firstname!=null && surname!=null 
      @             && (\forall int i; 
      @                     0<=i && i<students.length && students[i]!=null;
      @                         students[i].matrNr!=matrNr));
      @  signals_only ExamDataBaseException;
      @*/
    public abstract void addStudent(int matrNr, 
                                    String firstname, 
                                    String surname) 
						throws ExamDataBaseException;

    /**
     * Entfernt den Studenten mit der Matrikelnummer <code>matrNr</code> aus der Datenbasis,
     * falls ein solcher darin enthalten ist. Falls nicht, wird eine <code>ExamDataBaseException</code>
     * geworfen. Diese Methode ist dazu gedacht, Fehleingaben in die Datenbasis zu korrigieren.
     * Bei Abmeldungen von der Klausur ist die Methode <code>setBackedOut</code> zu verwenden.
     * @param matrNr die Matrikelnummer des zu l&ouml;schenden Studenten.
     * @throws ExamDataBaseException wird geworfen, falls kein Student mit der Matrikelnummer
     * <code>matrNr</code> in der Datenbasis enthalten ist.
     */
    /*@ public normal_behavior
      @  requires (\exists int i; 
      @                0<=i && i<students.length && students[i]!=null;
      @                    students[i].matrNr==matrNr);
      @  assignable students, students[*];
      @  ensures !(\exists int i; 
      @                0<=i && i<students.length && students[i]!=null;
      @                    students[i].matrNr==matrNr);
      @  ensures (\forall int i; 
      @               0<=i && i<students.length && students[i]!=null;
      @                   (\exists int j; 
      @                        0<=j && j<\old(students).length;
      @                            \old(students[j])==students[i]));
      @  ensures (\forall int i;
      @              0<=i && i<\old(students).length && \old(students[i])!=null
      @              && \old(students[i]).matrNr != matrNr;
      @                  (\exists int j;
      @                       0<=j && j<students.length;
      @                           students[j]==\old(students[i])));
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i]!=null;
      @                     students[i].matrNr==matrNr);
      @  signals_only ExamDataBaseException;
      @*/
    public abstract void deleteStudent(int matrNr) throws ExamDataBaseException;


    /** 
     * Setzt die Punktzahl des Studenten mit der Matrikelnummer <code>matrNr</code>
     * auf <code>points</code>.
     * @param matrNr die Matrikelnummer. Ein Student mit dieser Matrikelnummer mu&szlig; in der
     *  Datenbasis enthalten sein.
     * @param points die Punktzahl des Studenten mit der Matrikelnummer <code>matrNr</code>.
     *  Mu&szlig; zwischen -1 und <code>maxPoints</code> liegen.
     * @throws ExamDataBaseException wird geworfen wenn kein Student mit Matrikelnummer
     * <code>matrNr</code>, der nicht von der Klausur zur&uuml;ckgetreten ist, 
     * in der Datenbasis enthalten ist, oder <code>points</code> nicht
     * im Bereich zwischen -1 und <code>maxPoints</code> liegt.
     */
    /*@ public normal_behavior
      @  requires (\exists int i; 
      @                0<=i && i<students.length && students[i]!=null
      @                && students[i].matrNr==matrNr)
      @           && -1<=points && points<=maxPoints;
      @  assignable students[*].points;
      @  ensures (\forall int i; 
      @                0<=i && i<students.length && students[i]!=null;
      @                students[i].matrNr==matrNr ? students[i].points == points : 
      @                                             students[i].points==\old(students[i].points));
      @ also public exceptional_behavior
      @  requires !((\exists int i; 
      @                  0<=i && i<students.length && students[i]!=null
      @                  && students[i].matrNr==matrNr)
      @             && -1<=points && points<=maxPoints);
      @  signals_only ExamDataBaseException;
      @*/
    public abstract void setPoints(int matrNr, int points) 
						throws ExamDataBaseException;

    /*@ public normal_behavior
      @  ensures \result==threshold;
      @*/
    public abstract /*@pure@*/ int threshold();


    /*@ public normal_behavior
      @  ensures \result==step;
      @*/
    public abstract /*@pure@*/ int step();


    /*@ public normal_behavior
      @  ensures \result==maxPoints;
      @*/
    public abstract /*@pure@*/ int maxPoints(); 

    /**
     * Liefert die Matrikelnummern aller in der Datenbasis enthaltenen
     * Studenten als Array zur&uuml;ck.
     * @return Ein Integerarray bestehend aus den Matrikelnummern der in 
     * der Datenbasis enthaltenen Studenten.
     */
    /*@ public normal_behavior
      @  ensures (\forall int mnr; ;
      @               (\exists int i; ;
      @                    0<=i && i<students.length && students[i]!=null
      @                    && students[i].matrNr==mnr) 
      @               <==> (\exists int j;;
      @                         0<=j && j<\result.length && \result[j]==mnr));
      @  
      @*/
    public abstract int[] getMatrNrs();

    /**
     * Liefert den Vornamen des Studenten mit der Matrikelnummer <code>matrNr</code>
     * zur&uuml;ck, falls ein solcher in der Datenbasis enthalten ist. Andernfalls
     * wird eine <code>ExamDataBaseException</code> geworfen.
     * @return der Vorname des in der Datenbasis enthaltenen Studenten mit der
     * Matrikelnummer <code>matrNr</code>.
     * @throws ExamDataBaseException falls kein Student mit Matrikelnummer
     * <code>matrNr</code> in der Datenbasis vorkommt.
     */
    /*@ public normal_behavior
      @  requires (\exists int i; 
      @                0<=i && i<students.length && students[i]!=null
      @                && students[i].matrNr==matrNr);
      @  assignable \nothing;
      @  ensures (\exists int i; 
      @               students[i].matrNr==matrNr
      @               && \result==students[i].firstname);
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i]!=null
      @                 && students[i].matrNr==matrNr);

      @  signals_only ExamDataBaseException;
      @*/
    public abstract String getFirstname(int matrNr) 
						throws ExamDataBaseException;

    /**
     * Liefert den Nachnamen des Studenten mit der Matrikelnummer <code>matrNr</code>
     * zur&uuml;ck, falls ein solcher in der Datenbasis enthalten ist. Andernfalls
     * wird eine <code>ExamDataBaseException</code> geworfen.
     * @return der Nachname des in der Datenbasis enthaltenen Studenten mit der
     * Matrikelnummer <code>matrNr</code>.
     * @throws ExamDataBaseException falls kein Student mit Matrikelnummer
     * <code>matrNr</code> in der Datenbasis vorkommt.
     */
    /*@ public normal_behavior
      @  requires (\exists int i; 
      @                0<=i && i<students.length && students[i]!=null
      @                && students[i].matrNr==matrNr);
      @  assignable \nothing;
      @  ensures (\exists int i; 
      @               students[i].matrNr==matrNr
      @               && \result==students[i].surname);
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i]!=null
      @                 && students[i].matrNr==matrNr);

      @  signals_only ExamDataBaseException;
      @*/
    public abstract String getSurname(int matrNr) 
						throws ExamDataBaseException;

    /**
     * Liefert die Punkte des Studenten mit der Matrikelnummer <code>matrNr</code>
     * zur&uuml;ck, falls ein solcher in der Datenbasis enthalten ist. Andernfalls
     * wird eine <code>ExamDataBaseException</code> geworfen.
     * @return die Punkte des in der Datenbasis enthaltenen Studenten mit der
     * Matrikelnummer <code>matrNr</code>.
     * @throws ExamDataBaseException falls kein Student mit Matrikelnummer
     * <code>matrNr</code> in der Datenbasis vorkommt.
     */
    /*@ public normal_behavior
      @  requires (\exists int i; 
      @                0<=i && i<students.length && students[i]!=null
      @                && students[i].matrNr==matrNr);
      @  assignable \nothing;
      @  ensures (\exists int i; 
      @               students[i].matrNr==matrNr
      @               && \result==students[i].points);
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i]!=null
      @                 && students[i].matrNr==matrNr);
 
      @  signals_only ExamDataBaseException;
      @*/
    public abstract int getPoints(int matrNr) 
						throws ExamDataBaseException;

    /**
     * Liefert die Note des Studenten mit der Matrikelnummer <code>matrNr</code>
     * zur&uuml;ck, falls ein solcher in der Datenbasis enthalten ist und nicht
     * von der Klausur zur&uuml;ckgetreten ist. Andernfalls
     * wird eine <code>ExamDataBaseException</code> geworfen.
     * @return die Note des in der Datenbasis enthaltenen Studenten mit der
     * Matrikelnummer <code>matrNr</code>.
     * @throws ExamDataBaseException falls kein Student mit Matrikelnummer
     * <code>matrNr</code> in der Datenbasis vorkommt.
     */
    /*@ public normal_behavior
      @  requires (\exists int i; 
      @                0<=i && i<students.length && students[i] != null  
      @                && students[i].matrNr==matrNr);
      @  assignable \nothing;
      @  ensures (\exists int i; 
      @               students[i].matrNr==matrNr
      @               && \result==pointsToGrade(students[i].points, 
      @                                         0));
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i] != null 
      @                 && students[i].matrNr==matrNr);

      @  signals_only ExamDataBaseException;
      @*/
    public abstract int getGrade(int matrNr) 
						throws ExamDataBaseException;

    /**
     * Gibt genau dann <code>true</code> zur&uuml;ck, wenn f&uuml;r jeden in der
     * Datenbasis befindlichen Studenten, der nicht von der Klausur
     * zur&uuml;ckgetreten ist ein g&uuml;ltiger Punktestand
     * gr&ouml;&szlig;er 0 eingetragen wurde.
     * @return <code>true</code> gdw. f&uuml;r jeden in der
     * Datenbasis befindlichen Studenten, der nicht von der Klausur
     * zur&uuml;ckgetreten ist ein g&uuml;ltiger Punktestand
     * gr&ouml;&szlig;er 0 eingetragen wurde.
     */
    /*@ public normal_behavior
      @  ensures \result == (\forall int i; 
      @                          0<=i && i<students.length && students[i] != null; 
      @                              students[i].points>=0);
      @*/
    public abstract /*@pure@*/ boolean consistent();
    
}
