package de.ovgu.featureide.fm.core.conf.nodes;

public class Not2 extends Expression {

	public Not2(Variable child) {
		super(new Variable[] { child });
	}

	@Override
	protected byte computeValue() {
		switch (children[0].getValue()) {
		case TRUE:
			return FALSE;
		case FALSE:
			return TRUE;
		default:
			return UNDEFINED;
		}
	}

}
