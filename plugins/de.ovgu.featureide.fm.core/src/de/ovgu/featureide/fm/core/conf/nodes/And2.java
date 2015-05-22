package de.ovgu.featureide.fm.core.conf.nodes;

public class And2 extends Expression {

	private static final long serialVersionUID = 8373469012995551048L;

	public And2(Variable[] children) {
		super(children);
	}

	@Override
	protected int computeValue() {
		byte ret = TRUE;
		for (int i = 0; i < children.length; i++) {
			final int childValue = children[i].getValue();
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
