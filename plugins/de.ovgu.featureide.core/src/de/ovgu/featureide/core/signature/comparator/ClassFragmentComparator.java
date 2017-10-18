/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.signature.comparator;

import java.io.Serializable;
import java.util.Comparator;

import de.ovgu.featureide.core.signature.base.AbstractClassFragment;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;

//TODO MPL: better implementation
public class ClassFragmentComparator implements Comparator<AbstractClassFragment>, Serializable {

	private static final long serialVersionUID = -322298330373445431L;

	private final String favoritClass;

	public ClassFragmentComparator(String favoritClass) {
		if (favoritClass == null) {
			this.favoritClass = null;
		} else {
			this.favoritClass = favoritClass.toLowerCase();
		}
	}

	@Override
	public int compare(AbstractClassFragment sig0, AbstractClassFragment sig1) {
		return buildCompareString(sig0).compareTo(buildCompareString(sig1));
	}

	private String buildCompareString(AbstractClassFragment frag) {
		final String sigClassName;
		final AbstractClassSignature fragmentSignature = frag.getSignature();
		AbstractClassSignature parentSig = fragmentSignature.getParent();
		if (parentSig != null) {
			while (parentSig.getParent() != null) {
				parentSig = parentSig.getParent();
			}
			sigClassName = parentSig.getName();
		} else {
			sigClassName = fragmentSignature.getName();
		}

		return (sigClassName.toLowerCase().equals(favoritClass) ? 'a' : 'b') + fragmentSignature.getName().toLowerCase();
	}
}
