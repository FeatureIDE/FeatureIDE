public class ExamDataBaseImpl {
	
    public /*@pure@*/ int getNumParticipants() {
    	int num=0;
    	//@ loop_invariant 
    	//@     i>=0 && num>=0 
    	//@     && num==(\num_of int j; 
    	//@                  0<=j && j<i; validStudent(students[j]));
    	//@ assignable i, num;
    	//@ decreasing students.length-i;
    	//@
        for(int i=0; i<students.length; i++){
            if(validStudent(students[i])){
        	num++;
            }
        }
        return num;
    }
        
    public int getNumWithGrade(int grade) throws ExamDataBaseException{
    	if(!consistent()){ 
    	    throw new ExamDataBaseException("Tried to get average in inconsistent state");
        }
        int num=0;
    	//@ loop_invariant 
        //@     i>=0 && num>=0
        //@     && num==(\num_of int j;
    	//@                  0<=j && j<i; validStudent(students[j]) 
        //@                  && grade==pointsToGrade(students[j].points, 
    	//@		                             students[j].getBonusPoints()));
    	//@ assignable i, num;
    	//@ decreasing students.length-i;
    	//@
    	for(int i=0; i<students.length; i++){
    	    if(validStudent(students[i])){
	    		int g = pointsToGrade(students[i].points, 
	    			              students[i].getBonusPoints());
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
      //@                  0<=j && j<i; validStudent(students[j]) ?
      //@                      pointsToGrade(students[j].points, 
      //@                                    students[j].getBonusPoints()) : 0) 
      //@     && num==(\num_of int j;
      //@                  0<=j && j<i; validStudent(students[j]));
      //@ assignable i, sum, num;
      //@ decreasing students.length-i;
     
    	for(int i=0; i<students.length; i++){
    	    if(validStudent(students[i])){
	    		sum += pointsToGrade(students[i].points, 
	    			             students[i].getBonusPoints());
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
    	//@                  0<=j && j<i; validStudent(students[j])
    	//@                  && pointsToGrade(students[j].points,
    	//@                                   students[j].getBonusPoints())<500?
    	//@                      pointsToGrade(students[j].points, 
    	//@                                    students[j].getBonusPoints()) : 0);
    	//@ assignable i, sum;
    	//@ decreasing students.length-i;
    	 
    	for(int i=0; i<students.length; i++){
    	    if(validStudent(students[i])) {
	    		int grade = pointsToGrade(students[i].points, 
	    					  students[i].getBonusPoints());
	    		if(grade<500) {
	    		    sum+=grade;
	    		}
    	    }
    	}
    	int numPassed = getNumParticipants()-getNumWithGrade(500);
		return (numPassed==0 ? -1 : sum/numPassed);
    }

}
