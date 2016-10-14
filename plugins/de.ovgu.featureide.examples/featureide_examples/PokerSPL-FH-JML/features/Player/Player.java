/*
 * 
 */


/**
 * A poker player.
 */
public /*@nullable_by_default@*/ class Player {
  /** The Constant MAX_PLAYERS_CARDS. */
  public static final int MAX_PLAYERS_CARDS = getMaxPlayerCards();


 

  /** Player cards. */
  private /*@spec_public@*/ Card[] cards = new Card[MAX_PLAYERS_CARDS];

  /** The name. */
  private /*@spec_public@*/ int id;

  public static final Card[]  NO_CARDS = new Card[0];

  /*@ invariant id > 0;
      public invariant 0 == cards.length
                         | cards.length == MAX_PLAYERS_CARDS;
     
   */

 
  public Player(final int newId,
      final double initAmount) {
	 initPlayer(newId,initAmount);

  }

  /**
   * Instantiates a new player.
   * @param newId
   *          player's Id
   * @param initAmount
   *          the init amount
   */
  /*@ \conjunctive_contract
      requires newId > 0;
      assignable id;
      ensures id == newId ;
   */
  private void initPlayer(final int newId, final double initAmount){
	  this.id = newId;
  }


  /**
   * @return the name
   */
  /*@ public normal_behavior
      ensures \result > 0;
      ensures \result == id;
   */
  public final /*@pure@*/ int getId() {

    return this.id;
  }




  /**
   * Fold.
   */
  /*@ public normal_behavior
      assignable cards;
   */
  public final void fold() {
    //@ assert false;
    //@ assert false;
  }

 

  /**
   * Show cards.
   */
  /*@ public normal_behavior
      requires cards.length == MAX_PLAYERS_CARDS;
      requires NO_CARDS.length == 0;
      assignable cards;
      ensures cards.length == 0;
   */
  public final void showCards() {
    setCards(NO_CARDS);
    //@ assert false;
    //@ assert false;
  }

  /**
   * Stay.
   */
  /*@ public normal_behavior
      requires cards.length == MAX_PLAYERS_CARDS;
      ensures cards.length == MAX_PLAYERS_CARDS;
   */
  public final /*@pure@*/ void stay() {
    //@ assert false;
    //@ assert false;
  }




  /**
   * @param newCards Player's new cards.
   */
  /*@ requires 0 == newCards.length | newCards.length == MAX_PLAYERS_CARDS;
      assignable cards;
      ensures cards == newCards;
   */
  public final void setCards( /*@non_null@*/ Card[] newCards) {
    this.cards = newCards;
   
  }

  /**
   * @return Player's cards.
   */
  /*@ ensures \result == cards; */
  public final /*@pure@*/ Card[] getCards() {

    return cards;
  }
}
