
public abstract   class  ExamDataBase {
	

    
    protected /*@spec_public@*/ int maxPoints;

	

    
    protected /*@spec_public@*/ int threshold;

	/*@ 

     public  invariant
      0<threshold && threshold<=maxPoints; @*/

	
        

    
    protected /*@spec_public@*/ int step;

	/*@ 

     public  invariant
      0<step && step<=(maxPoints-threshold)/10; @*/

	
        

    
    protected /*@spec_public@*/ /*@nullable@*/ Student[] students;

	/*@ 

     public  invariant
      students!=null
      && (\forall int i; 
              0<=i && i<students.length && students[i]!=null;
                  (\forall ExamDataBase ex; ex!=null && ex!=this; (\forall int k;
                       0<=k && k<ex.students.length; ex.students[k]!=students[i]))
                  && -1<=students[i].points 
                  && students[i].points<=maxPoints 
                  && (\forall int j; 
                           0<=j && j<students.length 
                           && students[j]!=null && i!=j; 
                               students[i].matrNr!=students[j].matrNr)); @*/

	/*@ 
      

    
     protected normal_behavior
      ensures \result==pointsToGrade(points, bonusPoints); @*/
	
      
    protected /*@spec_public@*/ /*@pure@*/ int pointsToGrade(int points, 
							     int bonusPoints){
        points += (points<threshold 
        	   ? 0 
                   : (bonusPoints<=step 
                      ? bonusPoints 
                      : step));        
	return (points<threshold
                ? 500
                : ((points-threshold)/step>=9 
                   ? 100 
                   : (400 - 100*((points-threshold)/(3*step)) 
                          - (((points-threshold)/step)%3==1
                             ? 30 
                             : ((points-threshold)/step)%3==2 
                                ? 70 
                                : 0))));
    }

	/*@ 

    
     public normal_behavior
      requires 0<newThreshold && newThreshold<=newMaxPoints 
               && 0<newStep && newStep<=(newMaxPoints-newThreshold)/10;
      assignable threshold, step, maxPoints;
      ensures threshold==newThreshold 
              && step==newStep 
              && maxPoints==newMaxPoints;
     also public exceptional_behavior
      requires !(0<newThreshold && newThreshold<=newMaxPoints 
                 && 0<newStep && newStep<=(newMaxPoints-newThreshold)/10);

      signals_only ExamDataBaseException; @*/
	
        
    public abstract void setExamParameters(int newThreshold, 
                                           int newStep, 
                                           int newMaxPoints) 
						throws ExamDataBaseException;

	/*@ 

    
     public normal_behavior
      requires matrNr>0 && firstname!=null && surname!=null 
               && (\forall int i; 
                       0<=i && i<students.length && students[i]!=null;
                           students[i].matrNr!=matrNr);
      assignable students, students[*];
      ensures (\exists int i; 
                   0<=i && i<students.length && students[i]!=null; 
                       students[i].matrNr==matrNr 
                       && students[i].firstname==firstname 
                       && students[i].surname==surname 
                       && students[i].points==-1
                       && validStudent(students[i]));
      ensures (\forall int i; 
                   0<=i && i<students.length && students[i]!=null 
                   && students[i].matrNr != matrNr;      
                       (\exists int j; 
                            0<=j && j<\old(students).length;
                                \old(students[j])==students[i]));
      ensures (\forall int i;
                  0<=i && i<\old(students).length && \old(students[i])!=null;
                      (\exists int j;
                           0<=j && j<students.length;
                               students[j]==\old(students[i])));
     also public exceptional_behavior
      requires !(matrNr>0 && firstname!=null && surname!=null 
                 && (\forall int i; 
                         0<=i && i<students.length && students[i]!=null;
                             students[i].matrNr!=matrNr));
      signals_only ExamDataBaseException; @*/
	
      
    public abstract void addStudent(int matrNr, 
                                    String firstname, 
                                    String surname) 
						throws ExamDataBaseException;

	/*@ 

    
     public normal_behavior
      requires (\exists int i; 
                    0<=i && i<students.length && students[i]!=null;
                        students[i].matrNr==matrNr);
      assignable students, students[*];
      ensures !(\exists int i; 
                    0<=i && i<students.length && students[i]!=null;
                        students[i].matrNr==matrNr);
      ensures (\forall int i; 
                   0<=i && i<students.length && students[i]!=null;
                       (\exists int j; 
                            0<=j && j<\old(students).length;
                                \old(students[j])==students[i]));
      ensures (\forall int i;
                  0<=i && i<\old(students).length && \old(students[i])!=null
                  && \old(students[i]).matrNr != matrNr;
                      (\exists int j;
                           0<=j && j<students.length;
                               students[j]==\old(students[i])));
     also public exceptional_behavior
      requires !(\exists int i; 
                     0<=i && i<students.length && students[i]!=null;
                         students[i].matrNr==matrNr);
      signals_only ExamDataBaseException; @*/
	
      
    public abstract void deleteStudent(int matrNr) throws ExamDataBaseException;

	/*@ 


    
     public normal_behavior
      requires (\exists int i; 
                    0<=i && i<students.length && students[i]!=null
                    && students[i].matrNr==matrNr)
               && -1<=points && points<=maxPoints;
      assignable students[*].points;
      ensures (\forall int i; 
                    0<=i && i<students.length && students[i]!=null;
                    students[i].matrNr==matrNr ? students[i].points == points : 
                                                 students[i].points==\old(students[i].points));
     also public exceptional_behavior
      requires !((\exists int i; 
                      0<=i && i<students.length && students[i]!=null
                      && students[i].matrNr==matrNr)
                 && -1<=points && points<=maxPoints);
      signals_only ExamDataBaseException; @*/
	
      
    public abstract void setPoints(int matrNr, int points) 
						throws ExamDataBaseException;

	/*@ 

     public normal_behavior
      ensures \result==threshold; @*/
	
      
    public abstract /*@pure@*/ int threshold();

	/*@ 


     public normal_behavior
      ensures \result==step; @*/
	
      
    public abstract /*@pure@*/ int step();

	/*@ 


     public normal_behavior
      ensures \result==maxPoints; @*/
	
      
    public abstract /*@pure@*/ int maxPoints();

	/*@  

    
     public normal_behavior
      ensures (\forall int mnr; ;
                   (\exists int i; ;
                        0<=i && i<students.length && students[i]!=null
                        && students[i].matrNr==mnr) 
                   <==> (\exists int j;;
                             0<=j && j<\result.length && \result[j]==mnr)); @*/
	
      
      
    public abstract int[] getMatrNrs();

	/*@ 

    
     public normal_behavior
      requires (\exists int i; 
                    0<=i && i<students.length && students[i]!=null
                    && students[i].matrNr==matrNr);
      assignable \nothing;
      ensures (\exists int i; 
                   students[i].matrNr==matrNr
                   && \result==students[i].firstname);
     also public exceptional_behavior
      requires !(\exists int i; 
                     0<=i && i<students.length && students[i]!=null
                     && students[i].matrNr==matrNr);

      signals_only ExamDataBaseException; @*/
	
      
    public abstract String getFirstname(int matrNr) 
						throws ExamDataBaseException;

	/*@ 

    
     public normal_behavior
      requires (\exists int i; 
                    0<=i && i<students.length && students[i]!=null
                    && students[i].matrNr==matrNr);
      assignable \nothing;
      ensures (\exists int i; 
                   students[i].matrNr==matrNr
                   && \result==students[i].surname);
     also public exceptional_behavior
      requires !(\exists int i; 
                     0<=i && i<students.length && students[i]!=null
                     && students[i].matrNr==matrNr);

      signals_only ExamDataBaseException; @*/
	
      
    public abstract String getSurname(int matrNr) 
						throws ExamDataBaseException;

	/*@ 

    
     public normal_behavior
      requires (\exists int i; 
                    0<=i && i<students.length && students[i]!=null
                    && students[i].matrNr==matrNr);
      assignable \nothing;
      ensures (\exists int i; 
                   students[i].matrNr==matrNr
                   && \result==students[i].points);
     also public exceptional_behavior
      requires !(\exists int i; 
                     0<=i && i<students.length && students[i]!=null
                     && students[i].matrNr==matrNr);
 
      signals_only ExamDataBaseException; @*/
	
      
    public abstract int getPoints(int matrNr) 
						throws ExamDataBaseException;

	/*@ 

    
     public normal_behavior
      requires (\exists int i; 
                    0<=i && i<students.length && validStudent(students[i])  
                    && students[i].matrNr==matrNr);
      assignable \nothing;
      ensures (\exists int i; 
                   students[i].matrNr==matrNr
                   && \result==pointsToGrade(students[i].points, 
                                             students[i].getBonusPoints()));
     also public exceptional_behavior
      requires !(\exists int i; 
                     0<=i && i<students.length && validStudent(students[i]) 
                     && students[i].matrNr==matrNr);

      signals_only ExamDataBaseException; @*/
	
      
    public abstract int getGrade(int matrNr) 
						throws ExamDataBaseException;

	/*@ 

    
     public normal_behavior
      ensures \result == (\forall int i; 
                              0<=i && i<students.length && validStudent(students[i]); 
                                  students[i].points>=0); @*/
	
      
    public abstract /*@pure@*/ boolean consistent();


	
    
     private /*@pure@*/ boolean  validStudent__wrappee__BonusPoints  (Student student) {
    	return student != null;
    }


	

    public /*@pure@*/ boolean validStudent(Student student) {
    	return validStudent__wrappee__BonusPoints(student) && !student.backedOut;
    }

	/*@ 

     public  invariant
     (\forall int i;  
              0<=i && i<students.length && students[i]!=null;
                  (\forall ExamDataBase ex; ex!=null && ex!=this; (\forall int k;
                       0<=k && k<ex.students.length; ex.students[k]!=students[i]))
                  && 0<=students[i].bonusPoints
                  && students[i].bonusPoints<=maxPoints); @*/

	/*@ 
      

    
     public normal_behavior
      requires (\exists int i; 
                    0<=i && i<students.length && students[i]!=null
                    && students[i].matrNr==matrNr)
               && 0<=bonusPoints && bonusPoints<=maxPoints;
      assignable students[*].bonusPoints;
      ensures (\forall int i; 
                    0<=i && i<students.length && students[i]!=null;
                    students[i].matrNr==matrNr ? students[i].bonusPoints == bonusPoints : 
                                                 students[i].bonusPoints==\old(students[i].bonusPoints));
     also public exceptional_behavior
      requires !((\exists int i; 
                      0<=i && i<students.length && students[i]!=null
                      && students[i].matrNr==matrNr)
                 && 0<=bonusPoints && bonusPoints<=maxPoints);
  
      signals_only ExamDataBaseException; @*/
	
      
    public abstract void setBonusPoints(int matrNr, int bonusPoints)
						throws ExamDataBaseException;

	/*@ 

    
     public normal_behavior
      requires (\exists int i; 
                    0<=i && i<students.length && students[i]!=null
                    && students[i].matrNr==matrNr);
      assignable \nothing;
      ensures (\exists int i; 
                   students[i].matrNr==matrNr
                   && \result==students[i].bonusPoints);
     also public exceptional_behavior
      requires !(\exists int i; 
                     0<=i && i<students.length && students[i]!=null
                     && students[i].matrNr==matrNr);

      signals_only ExamDataBaseException; @*/
	
      
    public abstract int getBonusPoints(int matrNr) 
						throws ExamDataBaseException;

	/*@ 

    
     public normal_behavior
      requires (\exists int i; 
                    0<=i && i<students.length && students[i]!=null
                    && students[i].matrNr==matrNr);
      assignable students[*].backedOut;
      ensures (\forall int i; 
                    0<=i && i<students.length && students[i]!=null;
                    students[i].matrNr==matrNr ? students[i].backedOut == backedOut : 
                                                 students[i].backedOut==\old(students[i].backedOut));
     also public exceptional_behavior
      requires !(\exists int i; 
                     0<=i && i<students.length && students[i]!=null
                     && students[i].matrNr==matrNr);
      signals_only ExamDataBaseException; @*/
	
      
    public abstract void setBackedOut(int matrNr, boolean backedOut) 
						throws ExamDataBaseException;

	/*@ 

    
    public normal_behavior
     requires (\exists int i; 
                   0<=i && i<students.length && students[i]!=null
                   && students[i].matrNr==matrNr);
     assignable \nothing;
     ensures (\exists int i; 
                  students[i].matrNr==matrNr
                  && \result==students[i].backedOut);
    also public exceptional_behavior
     requires !(\exists int i; 
                    0<=i && i<students.length && students[i]!=null
                    && students[i].matrNr==matrNr);
     signals_only ExamDataBaseException; @*/
	
     
    public abstract boolean getBackedOut(int matrNr) 
						throws ExamDataBaseException;

	/*@ 

        
     public normal_behavior
      ensures \result==(\num_of int i; 
                            0<=i && i<students.length; validStudent(students[i])); @*/
	
      
    public abstract /*@pure@*/ int getNumParticipants();

	/*@ 
    
     
     public normal_behavior
      requires consistent();
      assignable \nothing;
      ensures \result==(\num_of int i; 
                           0<=i && i<students.length; validStudent(students[i])
                           && pointsToGrade(students[i].points,
                                            students[i].getBonusPoints())==grade);
     also public exceptional_behavior
      requires !consistent();
      
      signals_only ExamDataBaseException; @*/
	
      
    public abstract int getNumWithGrade(int grade) 
						throws ExamDataBaseException;

	/*@ 

     
     public normal_behavior
      requires consistent();
      assignable \nothing;
      ensures \result==(getNumParticipants()==0
                        ? -1
                        : ((\sum int i; 
                               0<=i && i<students.length; 
                               validStudent(students[i])?
                                   pointsToGrade(students[i].points, 
                                                 students[i].getBonusPoints()):0)
                          /getNumParticipants()));
     also public exceptional_behavior
      requires !consistent();
  
      signals_only ExamDataBaseException; @*/
	
      
    public abstract int getAverage() throws ExamDataBaseException;

	/*@ 

    
     public normal_behavior
      requires consistent();
      assignable \nothing;
      ensures \result==(getNumParticipants()-getNumWithGrade(500)==0
                        ? -1
                        : ((\sum int i; 
                               0<=i && i<students.length; validStudent(students[i])
                               && pointsToGrade(students[i].points,
                                                students[i].getBonusPoints())<500?
                                   pointsToGrade(students[i].points, 
                                                 students[i].getBonusPoints()):0)
                          /(getNumParticipants()-getNumWithGrade(500))));
     also public exceptional_behavior
      requires !consistent();

      signals_only ExamDataBaseException; @*/
	
      
    public abstract int getPassedAverage() throws ExamDataBaseException;


}
