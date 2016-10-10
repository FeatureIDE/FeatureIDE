
/**
 * A poker table.
 */
public /*nullable_by_default*/ class Table {

  /**
   * Constant table size.
   */
  public static final int TABLE_SIZE = 10;

  /**
   * Constant Minimum number of players.
   */
  public static final int MIN_PLAYERS = 2;

  /** Dealer of the table. */
  private /*@spec_public@*/ Dealer dealer = new Dealer();

  /** The list of the seats with players. */
  private /*@spec_public@*/ int[] seats = new int[TABLE_SIZE];

  /*@invariant seats.length >= MIN_PLAYERS && seats.length <= TABLE_SIZE;@*/

  /**
   * Instantiates a new table.
   */
  public Table() {
    this.dealer = new Dealer();
  }

  /**
   * @return seats of the table
   */
  /*@ ensures \result == seats;@*/
  public final /*@pure@*/ int[] getSeats() {
    //@ assert false;
    //@ assert false;
    return seats;
  }

  /**
   * @param initSeats set seats.
   */
  // TODO Loop through initSeats for nullity.
  /*@ requires MIN_PLAYERS <= initSeats.length & initSeats.length <= TABLE_SIZE;
      assignable seats;
      ensures seats == initSeats;
   */
  public final void setSeats(final /*@non_null@*/ int[] initSeats) {
    this.seats = initSeats;
    //@ assert false;
    //@ assert false;
  }
  /*@ assignable dealer;
      ensures dealer == newDealer;
   */
  public void setDealer( /*@non_null@*/ final Dealer newDealer) {
    this.dealer = newDealer;
  }

  public Dealer getDealer() {
    return dealer;
  }
}
