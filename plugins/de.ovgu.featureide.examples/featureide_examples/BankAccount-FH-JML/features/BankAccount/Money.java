/**
 * TODO description
 */
public class Money {
	private /*@ spec_public @*/ int value = 0;
	
	/*@ ensures this.value == value; @*/
	public Money(int value) {
		this.value = value;
	}
	
	/*@ ensures this.value == value; @*/
	public void setValue(int value) {
		this.value = value;
	}
	
	/*@ ensures this.value == \old(this.value) + value; @*/
	public void updateValue(int value) {
		this.value += value;
	}
	
	/*@ ensures \result == value; @*/
	public /*@ pure @*/ int getValue() {
		return value;
	}
	
	/*@ ensures \result == value / 100; @*/
	public /*@ pure @*/ int getCents() {
		return value / 100;
	}
	
	/*@ ensures \result == value % 100; @*/
	public /*@ pure @*/ int getFull() {
		return value % 100;
	}
}