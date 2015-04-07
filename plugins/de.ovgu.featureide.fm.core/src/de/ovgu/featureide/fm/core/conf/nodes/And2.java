package de.ovgu.featureide.fm.core.conf.nodes;

public class And2 extends Expression {
	
	public And2(Variable[] children) {
		super(children);
	}

	@Override
	protected byte computeValue() {
		byte ret = TRUE;
		for (int i = 0; i < children.length; i++) {
			final byte childValue = children[i].getValue();
			switch (childValue) {
			case FALSE:
				return FALSE;
			case UNDEFINED:
				ret = UNDEFINED;
			default:
				continue;
			}
		}
		return ret;
	}

}
