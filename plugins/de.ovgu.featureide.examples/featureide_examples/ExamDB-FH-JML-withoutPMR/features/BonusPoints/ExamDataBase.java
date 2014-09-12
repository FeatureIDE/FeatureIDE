/**
 * Abstrakte ExamDataBase Klasse. Speichert Benotungsparameter, Teilnehmerdaten
 * und erm&ouml;glicht Abfragen der Datenbasis.
 */
public abstract class ExamDataBase {

    /*@ public invariant
      @ (\forall int i;  
      @          0<=i && i<students.length && students[i]!=null;
      @              (\forall ExamDataBase ex; ex!=null && ex!=this; (\forall int k;
      @                   0<=k && k<ex.students.length; ex.students[k]!=students[i]))
      @              && 0<=students[i].bonusPoints
      @              && students[i].bonusPoints<=maxPoints);
      @*/

    /** 
     * Setzt die Bonuspunktzahl des Studenten mit der Matrikelnummer <code>matrNr</code>
     * auf <code>bonusPoints</code>.
     * @param matrNr die Matrikelnummer. Ein Student mit dieser Matrikelnummer mu&szlig; in der
     *  Datenbasis enthalten sein.
     * @param bonusPoints die Bonuspunktzahl des Studenten mit der Matrikelnummer <code>matrNr</code>.
     *  Mu&szlig; zwischen 0 und <code>maxPoints</code> liegen.
     * @throws ExamDataBaseException wird geworfen wenn kein Student mit Matrikelnummer
     *  <code>matrNr</code> in der Datenbasis enthalten ist, oder <code>bonusPoints</code> nicht
     *  im Bereich zwischen 0 und <code>maxPoints</code> liegt.
     */
    /*@ public normal_behavior
      @  requires (\exists int i; 
      @                0<=i && i<students.length && students[i]!=null
      @                && students[i].matrNr==matrNr)
      @           && 0<=bonusPoints && bonusPoints<=maxPoints;
      @  assignable students[*].bonusPoints;
      @  ensures (\forall int i; 
      @                0<=i && i<students.length && students[i]!=null;
      @                students[i].matrNr==matrNr ? students[i].bonusPoints == bonusPoints : 
      @                                             students[i].bonusPoints==\old(students[i].bonusPoints));
      @ also public exceptional_behavior
      @  requires !((\exists int i; 
      @                  0<=i && i<students.length && students[i]!=null
      @                  && students[i].matrNr==matrNr)
      @             && 0<=bonusPoints && bonusPoints<=maxPoints);
  
      @  signals_only ExamDataBaseException;
      @*/
    public abstract void setBonusPoints(int matrNr, int bonusPoints)
						throws ExamDataBaseException;

    /**
     * Liefert die Bonuspunkte des Studenten mit der Matrikelnummer <code>matrNr</code>
     * zur&uuml;ck, falls ein solcher in der Datenbasis enthalten ist. Andernfalls
     * wird eine <code>ExamDataBaseException</code> geworfen.
     * @return die Bonuspunkte des in der Datenbasis enthaltenen Studenten mit der
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
      @               && \result==students[i].bonusPoints);
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i]!=null
      @                 && students[i].matrNr==matrNr);

      @  signals_only ExamDataBaseException;
      @*/
    public abstract int getBonusPoints(int matrNr) 
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
      @                                         students[i].bonusPoints));
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i] != null 
      @                 && students[i].matrNr==matrNr);

      @  signals_only ExamDataBaseException;
      @*/
    public abstract int getGrade(int matrNr) 
						throws ExamDataBaseException;

}
