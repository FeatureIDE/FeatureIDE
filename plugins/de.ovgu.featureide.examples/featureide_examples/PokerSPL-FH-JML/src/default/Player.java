



public /*@nullable_by_default@*/    class  Player {
	
  
  public static final int MAX_PLAYERS_CARDS = getMaxPlayerCards();

	


 

  
  private /*@spec_public@*/ Card[] cards = new Card[MAX_PLAYERS_CARDS];

	

  
  private /*@spec_public@*/ int id;

	

  public static final Card[]  NO_CARDS = new Card[0];

	/*@ 

   invariant id > 0; @*/

	/*@ 
      public  invariant 0 == cards.length
                         | cards.length == MAX_PLAYERS_CARDS; @*/


	
     
   

 
  public Player(final int newId,
      final double initAmount) {
	 initPlayer(newId,initAmount);

  }

	/*@ 

  
   requires newId > 0;
      assignable id;
      ensures id == newId ; @*/
	
   
  private void initPlayer(final int newId, final double initAmount){
	  this.id = newId;
  }

	/*@ 


  
   public normal_behavior
      ensures \result > 0;
      ensures \result == id; @*/
	
   
  public final /*@pure@*/ int getId() {

    return this.id;
  }

	/*@ 




  
   public normal_behavior
      assignable cards; @*/
	
   
  public final void fold() {
    //@ assert false;
    //@ assert false;
  }

	/*@ 

 

  
   public normal_behavior
      requires cards.length == MAX_PLAYERS_CARDS;
      requires NO_CARDS.length == 0;
      assignable cards;
      ensures cards.length == 0; @*/
	
   
  public final void showCards() {
    setCards(NO_CARDS);
    //@ assert false;
    //@ assert false;
  }

	/*@ 

  
   public normal_behavior
      requires cards.length == MAX_PLAYERS_CARDS;
      ensures cards.length == MAX_PLAYERS_CARDS; @*/
	
   
  public final /*@pure@*/ void stay() {
    //@ assert false;
    //@ assert false;
  }

	/*@ 




  
   requires 0 == newCards.length | newCards.length == MAX_PLAYERS_CARDS;
      assignable cards;
      ensures cards == newCards; @*/
	
   
  public final void setCards( /*@non_null@*/ Card[] newCards) {
    this.cards = newCards;
   
  }

	/*@ 

  
   ensures \result == cards; @*/
	 
  public final /*@pure@*/ Card[] getCards() {

    return cards;
  }


	
	private static int getMaxPlayerCards() {
	
		return 5;
	}


}
