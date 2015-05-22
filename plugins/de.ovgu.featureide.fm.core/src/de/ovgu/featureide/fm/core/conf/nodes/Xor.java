package de.ovgu.featureide.fm.core.conf.nodes;

public class Xor extends Expression {

	private static final long serialVersionUID = -7576777102725610734L;

	public Xor(Variable[] children) {
		super(children);
	}

	@Override
	protected int computeValue() {
		boolean containsTrue = false;
		boolean undefined = false;
		for (int i = 0; i < children.length; i++) {
			final int childValue = children[i].getValue();
			switch (childValue) {
			case TRUE:
				if (containsTrue) {
					return FALSE;
				} else {
					containsTrue = true;
				}
				break;
			case UNDEFINED:
				undefined = true;
				break;
			default:
				continue;
			}
		}
		return undefined ? UNDEFINED : containsTrue ? TRUE : FALSE;
	}

}
