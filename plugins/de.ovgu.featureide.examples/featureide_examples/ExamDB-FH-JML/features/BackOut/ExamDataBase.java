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

    public /*@pure@*/ boolean validStudent(Student student) {
    	return original(student) && !student.backedOut;
    }
    
}
