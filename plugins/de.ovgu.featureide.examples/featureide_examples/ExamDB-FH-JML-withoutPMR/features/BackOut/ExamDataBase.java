/**
 * Abstrakte ExamDataBase Klasse. Speichert Benotungsparameter, Teilnehmerdaten
 * und erm&ouml;glicht Abfragen der Datenbasis.
 */
public abstract class ExamDataBase {

    /** 
     * Vermerkt den Studenten mit der Matrikelnummer <code>matrNr</code> als
     * von der Klausur zur&uuml;ckgetreten oder macht die Abmeldung r&uuml;ckg&auml;ngig.
     * @param matrNr die Matrikelnummer. Ein Student mit dieser Matrikelnummer mu&szlig; in der
     *  Datenbasis enthalten sein.
     * @param backedOut <code>true</code> falls der Student sich abmeldet, <code>false</code>,
     *  falls er von der Abmeldung zur&uuml;cktritt.
     * @throws ExamDataBaseException wird geworfen falls kein Student mit Matrikelnummer
     *  <code>matrNr</code> in der Datenbasis existiert.
     */
    /*@ public normal_behavior
      @  requires (\exists int i; 
      @                0<=i && i<students.length && students[i]!=null
      @                && students[i].matrNr==matrNr);
      @  assignable students[*].backedOut;
      @  ensures (\forall int i; 
      @                0<=i && i<students.length && students[i]!=null;
      @                students[i].matrNr==matrNr ? students[i].backedOut == backedOut : 
      @                                             students[i].backedOut==\old(students[i].backedOut));
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i]!=null
      @                 && students[i].matrNr==matrNr);
      @  signals_only ExamDataBaseException;
      @*/
    public abstract void setBackedOut(int matrNr, boolean backedOut) 
						throws ExamDataBaseException;

    /**
     * Ist ein Student mit der Matrikelnummer <code>matrNr</code> in der Datenbasis
     * enthalten, wird genau dann <code>true</code> zur&uuml;ckgeliefert, wenn
     * dieser Studenten von der Klausur zur&uuml;ckgetreten ist. Ist kein solcher Student
     * in der Datenbasis zu finden, wird eine <code>ExamDataBaseException</code> geworfen.
     * @return <code>true</code> gdw. der in der Datenbasis enthaltene Studenten mit der
     * Matrikelnummer <code>matrNr</code> von der Klausur zur&uuml;ckgetreten ist.
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
     @               && \result==students[i].backedOut);
     @ also public exceptional_behavior
     @  requires !(\exists int i; 
     @                 0<=i && i<students.length && students[i]!=null
     @                 && students[i].matrNr==matrNr);
     @  signals_only ExamDataBaseException;
     @*/
    public abstract boolean getBackedOut(int matrNr) 
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
    /*@ \consecutive_contract
      @ public normal_behavior
      @  requires matrNr>0 && firstname!=null && surname!=null 
      @           && (\forall int i; 
      @                   0<=i && i<students.length && students[i]!=null;
      @                       students[i].matrNr!=matrNr);
      @  assignable students, students[*];
      @  ensures (\exists int i; 
      @               0<=i && i<students.length && students[i]!=null; 
      @	                  !students[i].backedOut);
      @*/
    public abstract void addStudent(int matrNr, 
                                    String firstname, 
                                    String surname) 
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
      @                0<=i && i<students.length && students[i] != null && !students[i].backedOut  
      @                && students[i].matrNr==matrNr);
      @  assignable \nothing;
      @  ensures (\exists int i; 
      @               students[i].matrNr==matrNr
      @               && \result==pointsToGrade(students[i].points, 
      @                                         0));
      @ also public exceptional_behavior
      @  requires !(\exists int i; 
      @                 0<=i && i<students.length && students[i] != null && !students[i].backedOut 
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
      @                          0<=i && i<students.length && students[i] != null && !students[i].backedOut; 
      @                              students[i].points>=0);
      @*/
    public abstract /*@pure@*/ boolean consistent();
    
}
