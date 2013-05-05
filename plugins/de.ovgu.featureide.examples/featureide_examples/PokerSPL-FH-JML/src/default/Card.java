

public   class  Card {
	

  
  public static final int MIN_SUIT = 0;

	

  
  public static final int MAX_SUIT = 3;

	

  
  public static final int MIN_RANK = 2;

	

  
  public static final int MAX_RANK = 14;

	

  
  private /*@spec_public@*/ int suit;

	

  
  private /*@spec_public@*/ int rank;

	/*@ 

  //@ public invariant MIN_RANK <= rank & rank <= MAX_RANK;
  //@ public invariant MIN_SUIT <= suit & suit <= MAX_SUIT;

  
    public normal_behavior
       requires MIN_RANK <= cardRank & cardRank <= MAX_RANK;
       requires MIN_SUIT <= cardSuit & cardSuit <= MAX_SUIT ;
       assignable rank, suit;
       ensures rank == cardRank;
       ensures suit == cardSuit; @*/
	
    
  public Card(final int cardRank, final int cardSuit) {
    this.rank = cardRank;
    this.suit = cardSuit;
  }

	/*@ 

  
   public normal_behavior
      requires MIN_RANK <= newRank && newRank <= MAX_RANK;
      assignable rank;
      ensures rank == newRank; @*/
	
   
  public final void setRank(final int newRank) {
    this.rank = newRank;
    //@ assert false;
    //@ assert false;
  }


	

  
  //@ ensures \result == rank;
  public final /*@pure@*/ int getRank() {
    //@ assert false;
    //@ assert false;
    return this.rank;
  }

	/*@ 

  
   public normal_behavior
      requires MIN_SUIT <= newSuit && newSuit <= MAX_SUIT;
      assignable suit;
      ensures suit == newSuit; @*/
	
   
  public final void setSuit(final int newSuit) {
    suit = newSuit;
    //@ assert false;
    //@ assert false;
  }

	/*@ 

  
   ensures \result == suit; @*/
	
  public final /*@pure@*/ int getSuit() {
    //@ assert false;
    //@ assert false;
    return suit;
  }

	


 public static  class  Suit {
		
    public static final int CLUBS = 0;

		
    public static final int DIAMONDS = 1;

		
    public static final int HEARTS = 2;

		
    public static final int SPADES = 3;


	}

	

 public static  class  Rank {
		
    public static final int DEUCE = 2;

		
    public static final int THREE = 3;

		
    public static final int FOUR = 4;

		
    public static final int FIVE = 5;

		
    public static final int SIX = 6;

		
    public static final int SEVEN = 7;

		
    public static final int EIGHT = 8;

		
    public static final int NINE = 9;

		
    public static final int TEN = 10;

		
    public static final int JACK = 11;

		
    public static final int QUEEN = 12;

		
    public static final int KING = 13;

		
    public static final int ACE = 14;


	}


}
