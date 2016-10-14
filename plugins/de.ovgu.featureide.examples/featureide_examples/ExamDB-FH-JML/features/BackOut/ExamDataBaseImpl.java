public class ExamDataBaseImpl {

    public void setBackedOut(int matrNr, boolean backedOut) 
						throws ExamDataBaseException {
    	students[getIndex(matrNr)].backedOut = backedOut;
    }

    public boolean getBackedOut(int matrNr) throws ExamDataBaseException{
    	return students[getIndex(matrNr)].backedOut;
    }

}
