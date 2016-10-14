

/**
 * Dealer of the table.
 */
public /*nullable_by_default*/ class Dealer {

  /**
   * Number of cards of a full deck.
   */
  private static final int FULL_DECK = Deck.FULL_DECK;

  /**
   * Minimum number of players.
   */
  private static final int MIN_PLAYERS = Deck.MIN_PLAYERS;


  /** The button. */
  /*@spec_public@*/ private Button button;

  /** The deck. */
  /*@spec_public@*/ private Deck deck = new Deck();

 


  public Dealer(){
	  initDealer();
  }
  /**
   * Instantiates a new dealer.
   */
  private void initDealer() {
   
    //this.button = new Button();
    this.deck = new Deck();
 
  }
  
  public final void startGame(){
  }

  /*@ public normal_behavior
      requires deck != null;
      assignable deck.allCards;
      ensures deck.allCards.length == FULL_DECK;
   */
  public final void init(){
    getDeck().initilize();
  }
  
  /**
   * Deal flop.
   */
  /*@ assignable deck.allCards;
   ensures deck.allCards.length == \old(deck.allCards.length) - 3;*/
  public final void dealFlop() {
    //@ assert false;
    //@ assert false;
  }

  /**
   * Deal players.
   * @param numOfPlayers Number of players to be dealt cards.
   */
  /*@ requires numOfPlayers >= MIN_PLAYERS;
   requires deck.allCards.length == FULL_DECK;
   assignable deck.allCards;
   ensures deck.allCards.length == \old(deck.allCards.length) - 1;@*/
  public void dealPlayers(final int numOfPlayers) {
    //@ assert false;
    //@ assert false;
  }

  /**
   * Deal turn.
   */
  /*@ assignable deck.allCards;
   ensures deck.allCards.length == \old(allCards.length) - 1;@*/
  public void dealTurn() {
    //@ assert false;
    //@ assert false;
  }

  /**
   * Deal river.
   */
  /*@ assignable deck.allCards;
   ensures deck.allCards.length == \old(allCards.length) - 1;@*/
  public void dealRiver() {
    //@ assert false;
    //@ assert false;
  }

  /*@ assignable deck;
      ensures deck == newDeck;
   */
  public void setDeck( /*@non_null@*/ Deck newDeck) {
    this.deck = newDeck;
  }

  /*@ public normal_behavior
      requires deck != null;
      ensures 0 <= \result.allCards.length | \result.allCards.length <= FULL_DECK;
      ensures \result == deck;
   */
  public /*@pure@*/ Deck getDeck() {
    return deck;
  }

}
