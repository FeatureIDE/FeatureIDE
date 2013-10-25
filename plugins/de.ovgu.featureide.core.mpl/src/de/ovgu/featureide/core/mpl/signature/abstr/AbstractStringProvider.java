package de.ovgu.featureide.core.mpl.signature.abstr;

public abstract class AbstractStringProvider {
	protected static final String LINE_SEPARATOR = System.getProperty("line.separator");
	
	public abstract String getClassString(AbstractClassFragment cls, boolean shortString);
}
