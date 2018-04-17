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
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;

//TODO MPL: better implementation
public class SignatureComparator implements Comparator<Object>, Serializable {

	private static final long serialVersionUID = 7263887114849068283L;

	@Override
	public int compare(Object sig0, Object sig1) {
		return buildCompareString(sig0).compareTo(buildCompareString(sig1));
	}

	private String buildCompareString(Object obj) {
		final StringBuilder sb = new StringBuilder();
		if (obj instanceof AbstractSignature) {
			sb.append('b');
			if (obj instanceof AbstractMethodSignature) {
				sb.append('c');
			} else if (obj instanceof AbstractFieldSignature) {
				sb.append('b');
			} else if (obj instanceof AbstractClassSignature) {
				sb.append('a');
			} else {
				sb.append('d');
			}
			sb.append(((AbstractSignature) obj).getName().toLowerCase());
		} else if (obj instanceof AbstractClassFragment) {
			sb.append('a');
			sb.append(((AbstractClassFragment) obj).getSignature().getName().toLowerCase());
		}

		return sb.toString();
	}

}
