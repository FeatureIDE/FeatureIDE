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
package de.ovgu.featureide.core.signature;

import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;

import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.filter.base.IFilter;

/**
 * Holds the signature information for a whole java project.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public class ProjectSignatures implements Iterable<AbstractSignature> {

	public static final class SignatureIterator implements Iterator<AbstractSignature> {

		private final AbstractSignature[] signatureArray;

		private final LinkedList<IFilter<?>> filter = new LinkedList<>();
		private int count = 0;
		private boolean nextAvailable = false;

		public SignatureIterator() {
			signatureArray = new AbstractSignature[0];
		}

		private SignatureIterator(AbstractSignature[] signatureArray) {
			this.signatureArray = signatureArray;
		}

		public void addFilter(IFilter<?> filter) {
			this.filter.add(filter);
		}

		public void clearFilter() {
			filter.clear();
		}

		public void reset() {
			count = 0;
			nextAvailable = false;
		}

		private boolean findNext() {
			if ((filter == null) && (count < signatureArray.length)) {
				nextAvailable = true;
				return true;
			} else {
				for (; count < signatureArray.length; ++count) {
					if (isValid(signatureArray[count])) {
						nextAvailable = true;
						return true;
					}
				}
			}
			return false;
		}

		@SuppressWarnings({ "unchecked", "rawtypes" })
		private boolean isValid(AbstractSignature sig) {
			for (final IFilter curFilter : filter) {
				if (!curFilter.isValid(sig)) {
					return false;
				}
			}
			return true;
		}

		@Override
		public boolean hasNext() {
			return nextAvailable || findNext();
		}

		@Override
		public AbstractSignature next() {
			if (!nextAvailable && !findNext()) {
				return null;
			} else {
				nextAvailable = false;
				return signatureArray[count++];
			}
		}

		@Override
		public void remove() {}
	}

	private final String[] featureNames;
	private AbstractSignature[] signatureArray = null;

	private final IFeatureModel featureModel;

	private int hashCode = 0;
	private boolean hasHashCode = false;

	public ProjectSignatures(IFeatureModel featureModel) {
		this.featureModel = featureModel;
		final String[] tempFeatureNames = new String[featureModel.getNumberOfFeatures()];
		int countConcreteFeatures = 0;

		for (final IFeature feature : featureModel.getFeatures()) {
			if (feature.getStructure().isConcrete()) {
				tempFeatureNames[countConcreteFeatures++] = feature.getName();
			}
		}
		featureNames = new String[countConcreteFeatures];
		System.arraycopy(tempFeatureNames, 0, featureNames, 0, countConcreteFeatures);
	}

	@Override
	public SignatureIterator iterator() {
		return new SignatureIterator(signatureArray);
	}

	public SignatureIterator iterator(Collection<IFilter<?>> filters) {
		final SignatureIterator it = new SignatureIterator(signatureArray);
		for (final IFilter<?> filter : filters) {
			it.addFilter(filter);
		}
		return it;
	}

	public void sort(Comparator<AbstractSignature> comparator) {
		Arrays.sort(signatureArray, comparator);
	}

	public int[] getFeatureIDs(Collection<String> featureNames) {
		final int[] ids = new int[featureNames.size()];
		int i = 0;
		for (final String featureName : featureNames) {
			ids[i++] = getFeatureID(featureName);
		}
		return ids;
	}

	public int[] getFeatureIDs() {
		final int[] featureIDs = new int[featureNames.length];
		int i = 0;
		for (final String string : featureModel.getFeatureOrderList()) {
			featureIDs[i++] = getFeatureID(string);
		}
		return featureIDs;
	}

	public int getFeatureID(String featureName) {
		for (int i = 0; i < featureNames.length; ++i) {
			if (featureNames[i].equals(featureName)) {
				return i;
			}
		}
		return -1;
	}

	public String getFeatureName(int id) {
		return featureNames[id];
	}

	public int getFeatureCount() {
		return featureNames.length;
	}

	public String[] getFeatureNames() {
		return featureNames;
	}

	public int getSize() {
		return signatureArray.length;
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public void setSignatureArray(AbstractSignature[] signatureArray) {
		this.signatureArray = signatureArray;
	}

	@Override
	public boolean equals(Object obj) {
		return (this == obj) || ((obj instanceof ProjectSignatures) && Arrays.equals(signatureArray, ((ProjectSignatures) obj).signatureArray));
	}

	@Override
	public int hashCode() {
		if (!hasHashCode) {
			hashCode = 1;
			hashCode += Arrays.hashCode(signatureArray);
			hasHashCode = true;
		}
		return hashCode;
	}

	@Override
	public String toString() {
		return Arrays.toString(signatureArray);
	}

	public HashMap<Integer, int[]> getStatisticNumbers() {
		final int[][] allCounters = new int[4][4];
		final HashMap<Integer, int[]> fs = new HashMap<Integer, int[]>();
		for (int i = 0; i < signatureArray.length; ++i) {
			final AbstractSignature signature = signatureArray[i];
			if (signature instanceof AbstractFieldSignature) {
				count(signature, allCounters[2], fs, 2);
			} else if (signature instanceof AbstractMethodSignature) {
				count(signature, allCounters[3], fs, 3);
			} else if (signature instanceof AbstractClassSignature) {
				if (signature.getParent() != null) {
					count(signature, allCounters[1], fs, 1);
				} else {
					count(signature, allCounters[0], fs, 0);
				}
			}
		}

		final int[] spl = new int[3];
		final int[] iface = new int[3];
		spl[0] = allCounters[0][1];
		spl[1] = allCounters[2][1];
		spl[2] = allCounters[3][1];
		iface[0] = allCounters[0][0];
		iface[1] = allCounters[2][0];
		iface[2] = allCounters[3][0];
		fs.put(-2, spl);
		fs.put(-3, iface);

		return fs;
	}

	private void count(AbstractSignature signature, int[] curCounter, HashMap<Integer, int[]> fs, int i) {
		final AFeatureData[] featureData = signature.getFeatureData();
		for (final AFeatureData feature : featureData) {
			int[] x = fs.get(feature.getID());
			if (x == null) {
				x = new int[] { 0, 0, 0, 0 };
				fs.put(feature.getID(), x);
			}
			x[i]++;
		}

		curCounter[0]++;
		curCounter[1] += signature.getFeatureData().length;
		if (signature.isPrivate()) {
			curCounter[2]++;
			curCounter[3] += signature.getFeatureData().length;
		}
	}

	public String getStatisticsString() {
		final int[][] allCounters = new int[4][4];
		final HashMap<Integer, int[]> fs = new HashMap<Integer, int[]>();

		for (int i = 0; i < signatureArray.length; ++i) {
			final AbstractSignature signature = signatureArray[i];
			if (signature instanceof AbstractFieldSignature) {
				count(signature, allCounters[2], fs, 2);
			} else if (signature instanceof AbstractMethodSignature) {
				count(signature, allCounters[3], fs, 3);
			} else if (signature instanceof AbstractClassSignature) {
				if (signature.getParent() != null) {
					count(signature, allCounters[1], fs, 1);
				} else {
					count(signature, allCounters[0], fs, 0);
					System.out.println(signature.getFullName());
				}
			}
		}

		final StringBuilder sb = new StringBuilder();
		for (int i = 0; i < allCounters.length; i++) {
			final int[] curCounter = allCounters[i];
			switch (i) {
			case 0:
				sb.append("#Classes: ");
				break;
			case 1:
				sb.append("#InnerClasses: ");
				break;
			case 2:
				sb.append("#Fields: ");
				break;
			case 3:
				sb.append("#Methods: ");
				break;
			default:
				break;
			}
			sb.append(curCounter[0]);
			sb.append("\n\t#Private: ");
			sb.append(curCounter[2]);
			sb.append("\n\t#Definitions: ");
			sb.append(curCounter[1]);
			sb.append("\n\t\t#Private Definitions: ");
			sb.append(curCounter[3]);
			sb.append("\n");
		}
		sb.append("\n\nPer Feature:");
		for (final Entry<Integer, int[]> entry : fs.entrySet()) {
			sb.append("\n\t");
			sb.append(entry.getKey());
			sb.append("\n");
			final int[] x = entry.getValue();
			for (int i = 0; i < x.length; i++) {
				switch (i) {
				case 0:
					sb.append("\t\t#Classes: ");
					break;
				case 1:
					sb.append("\t\t#InnerClasses: ");
					break;
				case 2:
					sb.append("\t\t#Fields: ");
					break;
				case 3:
					sb.append("\t\t#Methods: ");
					break;
				default:
					break;
				}
				sb.append(x[i]);
				sb.append("\n");
			}
		}
		return sb.toString();
	}
}
