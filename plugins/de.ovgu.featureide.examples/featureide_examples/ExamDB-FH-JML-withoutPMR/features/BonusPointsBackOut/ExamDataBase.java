/**
 * Abstrakte ExamDataBase Klasse. Speichert Benotungsparameter, Teilnehmerdaten
 * und erm&ouml;glicht Abfragen der Datenbasis.
 */
public abstract class ExamDataBase {

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
      @                0<=i && i<students.length && students[i] != null && !students[i].backedOut  
      @                && students[i].matrNr==matrNr);
      @  assignable \nothing;
      @  ensures (\exists int i; 
      @               students[i].matrNr==matrNr
      @               && \result==pointsToGrade(students[i].points, 
      @                                         students[i].bonusPoints));
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i] != null && !students[i].backedOut   
      @                 && students[i].matrNr==matrNr);

      @  signals_only ExamDataBaseException;
      @*/
    public abstract int getGrade(int matrNr) 
						throws ExamDataBaseException;

}
