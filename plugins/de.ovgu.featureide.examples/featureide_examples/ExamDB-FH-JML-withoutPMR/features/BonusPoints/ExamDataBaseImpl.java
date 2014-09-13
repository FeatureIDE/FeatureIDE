public class ExamDataBaseImpl {

    public void setBonusPoints(int matrNr, int bonusPoints) 
						throws ExamDataBaseException{
		if(!(0<=bonusPoints && bonusPoints<=maxPoints)) {
		    throw new ExamDataBaseException("Tried to set invalid bonus points");
		}
        students[getIndex(matrNr)].bonusPoints = bonusPoints;
    }

    public int getBonusPoints(int matrNr) throws ExamDataBaseException{
        return students[getIndex(matrNr)].bonusPoints;
    }
   
    public int getGrade(int matrNr) throws ExamDataBaseException{
		int i=getIndex(matrNr);
    	if(students[i] != null){
    	    return pointsToGrade(students[i].points, students[i].bonusPoints);
    	}
    	throw new ExamDataBaseException("Matriculation number not found");
    }

}
