public class ExamDataBaseImpl {

    public void setBackedOut(int matrNr, boolean backedOut) 
						throws ExamDataBaseException {
    	students[getIndex(matrNr)].backedOut = backedOut;
    }

    public boolean getBackedOut(int matrNr) throws ExamDataBaseException{
    	return students[getIndex(matrNr)].backedOut;
    }

    public int getGrade(int matrNr) throws ExamDataBaseException{
		int i=getIndex(matrNr);
    	if(students[i] != null && !students[i].backedOut){
    	    return pointsToGrade(students[i].points, 0);
    	}
    	throw new ExamDataBaseException("Matriculation number not found");
    }

    public boolean consistent(){
    	//@ loop_invariant 
    	//@     (\forall int j; 
    	//@          0<=j && j<i && students[i] != null && !students[i].backedOut; 
    	//@              students[j].points >= 0) && i>=0;
    	//@ assignable i;
    	//@ decreasing students.length-i;

        for(int i=0; i<students.length; i++) {
		    if(students[i] != null && !students[i].backedOut 
	               && students[i].points < 0) {
			return false;
		    }
		}
		return true;
    }
    
}
