public class ExamDataBaseImpl {
	
    public /*@pure@*/ int getNumParticipants() {
    	int num=0;
    	//@ loop_invariant 
    	//@     i>=0 && num>=0 
    	//@     && num==(\num_of int j; 
    	//@                  0<=j && j<i; students[j] != null);
    	//@ assignable i, num;
    	//@ decreasing students.length-i;
    	//@
        for(int i=0; i<students.length; i++){
            if(students[i] != null){
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
    	//@                  0<=j && j<i; students[j] != null 
        //@                  && grade==pointsToGrade(students[j].points, 
    	//@		                             0));
    	//@ assignable i, num;
    	//@ decreasing students.length-i;
    	//@
    	for(int i=0; i<students.length; i++){
    	    if(students[i] != null){
	    		int g = pointsToGrade(students[i].points, 
	    			              0);
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
      //@                  0<=j && j<i; students[j] != null ?
      //@                      pointsToGrade(students[j].points, 
      //@                                    0) : 0) 
      //@     && num==(\num_of int j;
      //@                  0<=j && j<i; students[j] != null);
      //@ assignable i, sum, num;
      //@ decreasing students.length-i;
     
    	for(int i=0; i<students.length; i++){
    	    if(students[i] != null){
	    		sum += pointsToGrade(students[i].points, 
	    			             0);
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
    	//@                  0<=j && j<i; students[j] != null
    	//@                  && pointsToGrade(students[j].points,
    	//@                                   0)<500?
    	//@                      pointsToGrade(students[j].points, 
    	//@                                    0) : 0);
    	//@ assignable i, sum;
    	//@ decreasing students.length-i;
    	 
    	for(int i=0; i<students.length; i++){
    	    if(students[i] != null) {
	    		int grade = pointsToGrade(students[i].points, 
	    					  0);
	    		if(grade<500) {
	    		    sum+=grade;
	    		}
    	    }
    	}
    	int numPassed = getNumParticipants()-getNumWithGrade(500);
		return (numPassed==0 ? -1 : sum/numPassed);
    }

}
