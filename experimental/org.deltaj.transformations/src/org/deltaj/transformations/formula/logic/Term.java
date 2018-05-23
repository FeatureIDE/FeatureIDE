package org.deltaj.transformations.formula.logic;

public class Term implements Comparable<Term> {

	private final byte variableCount;
	private int values; // uses two bits for each variable

	private Term(byte variableCount, int values) {

		this.variableCount = variableCount;
		this.values = values;
	}

	public static Term fromConfiguration(byte variableCount, int configuration) {

		int expanded = 0;
		for (int i = 0; i < variableCount; ++i) {

			int mask = 1 << i;
			if ((configuration & mask) != 0) {

				expanded |= 1 << 2 * i;
			}
		}
		return new Term(variableCount, expanded);
	}

	public static Term parse(byte variableCount, String termText) {

		int parsedValues = new TermParser(variableCount, termText).parse();
		return new Term(variableCount, parsedValues);
	}

	public TermValue getValue(int index) {

		int value = values >> index * 2 & 3;
		return TermValue.values()[value];
	}

	private void setValue(int index, TermValue value) {

		values &= ~(3 << index * 2);
		values |= value.ordinal() << index * 2;
	}

	@Override
	public String toString() {

		StringBuilder builder = new StringBuilder();

		for (int i = 0; i < variableCount; ++i) {
			builder.append(getValue(i));
		}

		return builder.toString();
	}

	public int getCount(TermValue value) {

		int count = 0;

		for (int i = 0; i < variableCount; ++i) {
			if (getValue(i) == value) {
				++count;
			}
		}

		return count;
	}

	@Override
	public int compareTo(Term other) {

		for (int i = 0; i < variableCount; ++i) {
			int thisValue = getValue(i).ordinal();
			int otherValue = other.getValue(i).ordinal();

			if (thisValue != otherValue) {
				return thisValue - otherValue;
			}
		}
		return 0;
	}

	public boolean isTautology() {

		for (int i = 0; i < variableCount; ++i) {
			if (getValue(i) != TermValue.DONTCARE) {
				return false;
			}
		}
		return true;
	}

	public Term mergeIfPossible(Term other) {

		int differenceIndex = -1;
		int differenceCount = 0;

		for (int i = 0; i < variableCount; ++i) {
			if (getValue(i) != other.getValue(i)) {
				differenceIndex = i;
				++differenceCount;
			}
		}

		if (differenceCount == 1) {
			Term mergedTerm = new Term(variableCount, values);
			mergedTerm.setValue(differenceIndex, TermValue.DONTCARE);
			return mergedTerm;
		} else {
			return null;
		}
	}

	public boolean implies(Term other) {

		for (int i = 0; i < variableCount; ++i) {
			if (getValue(i) != other.getValue(i) && getValue(i) != TermValue.DONTCARE) {
				return false;
			}
		}
		return true;
	}
}
