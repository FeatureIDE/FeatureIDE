package de.ovgu.featureide.cloneanalysis.results;

import org.eclipse.core.runtime.IPath;

public class FeatureRootLocation {
	private IPath location;

	public FeatureRootLocation(IPath locationPath) {
		assert locationPath.toString() != null && !locationPath.toString().isEmpty() : "path must not be empty";
		assert locationPath.isAbsolute() : "path is not absolute";
		this.location = locationPath;
	}

	/**
	 * @return the location
	 */
	public IPath getLocation() {
		return location;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((location == null) ? 0 : location.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FeatureRootLocation other = (FeatureRootLocation) obj;
		if (location == null) {
			if (other.location != null)
				return false;
		} else if (!location.equals(other.location))
			return false;
		return true;
	}

}
