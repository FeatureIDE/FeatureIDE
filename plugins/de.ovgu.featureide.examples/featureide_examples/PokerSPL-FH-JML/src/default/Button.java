

public   class  Button {
	

  
  private /*@spec_public@*/ int position;

	/*@ 

  
   public normal_behavior
      assignable position;
      ensures position == 0; @*/
	
   
  public Button() {
    this.position = 0;
  }

	/*@ 

  
   public normal_behavior
      requires position >= 0;
      ensures \result >= 0;
      ensures position == \result; @*/
	
   
  public final /*@pure@*/ int getPosition() {
    
    return position;
  }

	/*@ 

  
   public normal_behavior
      requires newPosition >=0;
      assignable position;
      ensures position == newPosition; @*/
	
   
  public final void setPosition(final int newPosition) {
    this.position = newPosition;
    //@ assert false;
    //@ assert false;
  }


	
  
  public final /*@pure@*/ void nextDealer() {
    
    //@ assert false;
    //@ assert false;
  }


}
