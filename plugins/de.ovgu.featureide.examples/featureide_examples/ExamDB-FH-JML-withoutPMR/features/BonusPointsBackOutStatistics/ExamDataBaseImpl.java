public class ExamDataBaseImpl {
	
    public int getNumWithGrade(int grade) throws ExamDataBaseException{
    	if(!consistent()){ 
    	    throw new ExamDataBaseException("Tried to get average in inconsistent state");
        }
        int num=0;
    	//@ loop_invariant 
        //@     i>=0 && num>=0
        //@     && num==(\num_of int j;
    	//@                  0<=j && j<i; students[j] != null && !students[j].backedOut 
        //@                  && grade==pointsToGrade(students[j].points, 
    	//@		                             students[j].bonusPoints));
    	//@ assignable i, num;
    	//@ decreasing students.length-i;
    	//@
    	for(int i=0; i<students.length; i++){
    	    if(students[i] != null && !students[i].backedOut){
	    		int g = pointsToGrade(students[i].points, 
	    			              students[i].bonusPoints);
	    		if(grade==g){
	    		    num++;
                }
    	    }
    	}
    	return num;
    }

    public int getAverage() throws ExamDataBaseException{
    	if(!consistent()){
    	    throw new ExamDataBaseException("Tried to get average in inconsistent state");
    	}
    	int sum=0;
        int num=0;
      //@ loop_invariant 
      //@     i>=0
      //@     && sum==(\sum int j; 
      //@                  0<=j && j<i; students[j] != null && !students[j].backedOut ?
      //@                      pointsToGrade(students[j].points, 
      //@                                    students[j].bonusPoints) : 0) 
      //@     && num==(\num_of int j;
      //@                  0<=j && j<i; students[j] != null && !students[j].backedOut);
      //@ assignable i, sum, num;
      //@ decreasing students.length-i;
     
    	for(int i=0; i<students.length; i++){
    	    if(students[i] != null && !students[i].backedOut){
	    		sum += pointsToGrade(students[i].points, 
	    			             students[i].bonusPoints);
	            num++;
		    }
		}
		return (num==0 ? -1 : sum/num);
    }

    public int getPassedAverage() throws ExamDataBaseException{
    	if(!consistent()){ 
    	    throw new ExamDataBaseException("Tried to get average in inconsistent state");
        }
    	int sum=0;
    	//@ loop_invariant 
    	//@     i>=0
    	//@     && sum==(\sum int j; 
    	//@                  0<=j && j<i; students[j] != null && !students[j].backedOut
    	//@                  && pointsToGrade(students[j].points,
    	//@                                   students[j].bonusPoints)<500?
    	//@                      pointsToGrade(students[j].points, 
    	//@                                    students[j].bonusPoints) : 0);
    	//@ assignable i, sum;
    	//@ decreasing students.length-i;
    	 
    	for(int i=0; i<students.length; i++){
    	    if(students[i] != null && !students[i].backedOut) {
	    		int grade = pointsToGrade(students[i].points, 
	    					  students[i].bonusPoints);
	    		if(grade<500) {
	    		    sum+=grade;
	    		}
    	    }
    	}
    	int numPassed = getNumParticipants()-getNumWithGrade(500);
		return (numPassed==0 ? -1 : sum/numPassed);
    }

}
