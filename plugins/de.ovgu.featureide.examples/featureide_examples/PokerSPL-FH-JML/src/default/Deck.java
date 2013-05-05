


public   class  Deck {
	
  
  public static final int FULL_DECK = 52;

	

  
  public static final int MIN_PLAYERS = 2;

	

  private static final int MIN_RANK = Card.MIN_RANK;

	
  private static final int MAX_RANK = Card.MAX_RANK;

	
  private static final int MIN_SUIT = Card.MIN_SUIT;

	
  private static final int MAX_SUIT = Card.MAX_SUIT;

	
  
  
  private /*@spec_public@*/ /*@non_null@*/ Card[] allCards = new Card[FULL_DECK];

	/*@ 

  public  invariant 0 <= allCards.length & allCards.length <= FULL_DECK; @*/


	

  
  public Deck() {
    this.allCards = new Card[FULL_DECK];
  }

	/*@ 

  
   public normal_behavior
      requires allCards.length == FULL_DECK;
      assignable allCards;
      ensures allCards.length == FULL_DECK; @*/
	
   
  public final void shuffle() {

    //@ assert false;
    //@ assert false;
  }

	/*@ 
  
   public normal_behavior
      assignable allCards;
      ensures allCards.length == FULL_DECK; @*/
	
   
  public final void initilize(){
    allCards = new Card[FULL_DECK];
    int counter = 0;
    for (int i = MIN_RANK; i <= MAX_RANK; i++){
      for (int j = MIN_SUIT; j <= MAX_SUIT; j++){
        allCards[counter] = new Card(i,j);
        counter++;
      }
    }
  }

	/*@ 

  
   public normal_behavior
      ensures \result == allCards; @*/
	
   
  public final /*@pure@*/ Card[] getAllCards() {
    //@ assert false;
    //@ assert false;
    return allCards;
  }

	/*@ 

  
   public normal_behavior
      requires  0 <= newDeckOfCards.length & newDeckOfCards.length <= FULL_DECK;
      requires (\forall int i; 0<=i && i< newDeckOfCards.length; newDeckOfCards[i] != null);
      assignable allCards;
      ensures allCards == newDeckOfCards; @*/
	
   
  public final void setAllCards(final /*@non_null@*/ Card[] newDeckOfCards) {
    this.allCards = newDeckOfCards;
    //@ assert false;
    //@ assert false;
  }


}
