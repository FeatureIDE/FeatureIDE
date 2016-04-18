package de.ovgu.featureide.fm.core.conf.nodes;

public class Or2 extends Expression {

	private static final long serialVersionUID = 4681502418076739912L;

	public Or2(Variable[] children) {
		super(children);
	}

	@Override
	protected int computeValue() {
		byte ret = FALSE;
		for (int i = 0; i < children.length; i++) {
			final int childValue = children[i].getValue();
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
