package de.ovgu.featureide.fm.core.conf.nodes;

public class Or2 extends Expression {
	
	public Or2(Variable[] children) {
		super(children);
	}

	@Override
	protected byte computeValue() {
		byte ret = FALSE;
		for (int i = 0; i < children.length; i++) {
			final byte childValue = children[i].getValue();
			switch (childValue) {
			case TRUE:
				return TRUE;
			case UNDEFINED:
				ret = UNDEFINED;
			default:
				continue;
			}
		}
		return ret;
	}

}
