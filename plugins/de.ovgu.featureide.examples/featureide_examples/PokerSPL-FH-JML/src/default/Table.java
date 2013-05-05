

public   class  Table {
	

  
  public static final int TABLE_SIZE = 10;

	

  
  public static final int MIN_PLAYERS = 2;

	

  
  private /*@spec_public@*/ Dealer dealer = new Dealer();

	

  
  private /*@spec_public@*/ int[] seats = new int[TABLE_SIZE];

	/*@ 

  invariant seats.length >= MIN_PLAYERS && seats.length <= TABLE_SIZE; @*/


	

  
  public Table() {
    this.dealer = new Dealer();
  }

	/*@ 

  
   ensures \result == seats; @*/
	
  public final /*@pure@*/ int[] getSeats() {
    //@ assert false;
    //@ assert false;
    return seats;
  }

	/*@ 

  
  
   requires MIN_PLAYERS <= initSeats.length & initSeats.length <= TABLE_SIZE;
      assignable seats;
      ensures seats == initSeats; @*/
	
   
  public final void setSeats(final /*@non_null@*/ int[] initSeats) {
    this.seats = initSeats;
    //@ assert false;
    //@ assert false;
  }

	/*@ 
   assignable dealer;
      ensures dealer == newDealer; @*/
	
   
  public void setDealer( /*@non_null@*/ final Dealer newDealer) {
    this.dealer = newDealer;
  }


	

  public Dealer getDealer() {
    return dealer;
  }


}
