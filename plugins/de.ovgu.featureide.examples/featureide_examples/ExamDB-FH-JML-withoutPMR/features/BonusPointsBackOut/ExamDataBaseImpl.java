public class ExamDataBaseImpl {

    public int getGrade(int matrNr) throws ExamDataBaseException{
		int i=getIndex(matrNr);
    	if(students[i] != null && !students[i].backedOut){
    	    return pointsToGrade(students[i].points, students[i].bonusPoints);
    	}
    	throw new ExamDataBaseException("Matriculation number not found");
    }
    
}
