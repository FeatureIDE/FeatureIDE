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
    
// code from feature BackOut
    
    public /*@pure@*/ boolean backedOut = false; 
    
// code from feature BonusPoins
    
	public int bonusPoints = 0;

// code merged from feature ExamDB and BonusPoints
	
    private /*@pure helper@*/ int getBonusPoints__ExamDB() {
    	return 0;
    }

	public/* @pure@ */int getBonusPoints() {
		if (!FeatureModel.f(FeatureModel.BonusPoints))
			return getBonusPoints__ExamDB();
		return bonusPoints;
	}

}
