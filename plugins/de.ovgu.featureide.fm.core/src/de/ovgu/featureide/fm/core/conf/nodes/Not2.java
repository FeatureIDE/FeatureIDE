package de.ovgu.featureide.fm.core.conf.nodes;

public class Not2 extends Expression {

	private static final long serialVersionUID = 1021521732243130751L;

	public Not2(Variable child) {
		super(new Variable[] { child });
	}

	@Override
	protected int computeValue() {
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
