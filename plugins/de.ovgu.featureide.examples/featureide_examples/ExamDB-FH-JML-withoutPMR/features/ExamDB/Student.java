public class Student {

	/*@ public invariant
      @  matrNr>0 && firstname != null && surname != null;
      @*/

    public final int matrNr;
    
    public final String firstname;
    
    public final String surname;

    public int points = -1;

    public Student(int matrNr, String firstname, String surname){
		this.matrNr = matrNr;
		this.firstname = firstname;
		this.surname = surname;
    }
    
}
