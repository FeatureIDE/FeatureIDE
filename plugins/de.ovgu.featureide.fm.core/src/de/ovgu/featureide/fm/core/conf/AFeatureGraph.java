/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.conf;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;

public abstract class AFeatureGraph implements IFeatureGraph {

	private static final long serialVersionUID = 1L;

	public static final byte EDGE_NONE = 0b00000000, EDGE_11 = 0b00000100, //0x04,
			EDGE_10 = 0b00001000, //0x08,
			EDGE_1Q = 0b00001100, //0x0c,
			EDGE_01 = 0b00010000, //0x10,
			EDGE_00 = 0b00100000, //0x20,
			EDGE_0Q = 0b00110000, //0x30;
			VALUE_NONE = 0b00000000, //0x02;
			VALUE_1 = 0b00000001, //0x02;
			VALUE_0 = 0b00000010, //0x01;
			VALUE_Q = 0b00000011; //0x03;

	public static final byte MASK_1_11110011 = (byte) 0b11110011, //0xf3,
			MASK_0_11001111 = (byte) 0b11001111, //0xcf,
			MASK_1_00001100 = ~MASK_1_11110011, MASK_0_00110000 = ~MASK_0_11001111;

	protected final String[] featureArray;
	protected final String[] coreFeatures;
	protected final String[] deadFeatures;

	protected final int size;
	protected final HashMap<String, Integer> featureMap;
	protected final ArrayList<LinkedList<Expression>> expListAr;

	public static boolean isEdge(byte edge, byte q) {
		switch (q) {
		case EDGE_NONE:
			return edge == EDGE_NONE;
		case EDGE_11:
		case EDGE_10:
		case EDGE_1Q:
			return (edge & MASK_1_00001100) == q;
		case EDGE_01:
		case EDGE_00:
		case EDGE_0Q:
			return (edge & MASK_0_00110000) == q;
		default:
			return false;
		}
	}

	public AFeatureGraph(Collection<Feature> variantfeatures, Collection<Feature> coreFeatures, Collection<Feature> deadFeatures) {
		size = variantfeatures.size();
		featureMap = new HashMap<>(size << 1);
		featureArray = new String[size];
		this.coreFeatures = new String[coreFeatures.size()];
		this.deadFeatures = new String[deadFeatures.size()];

		expListAr = new ArrayList<>(size);
		for (int i = 0; i < size; i++) {
			expListAr.add(null);
		}

		int i = 0;
		for (Feature feature : coreFeatures) {
			this.coreFeatures[i++] = feature.getName();
		}

		i = 0;
		for (Feature feature : deadFeatures) {
			this.deadFeatures[i++] = feature.getName();
		}

		i = 0;
		for (Feature feature : variantfeatures) {
			featureArray[i++] = feature.getName();
		}

		Arrays.sort(featureArray);
		Arrays.sort(this.coreFeatures);
		Arrays.sort(this.deadFeatures);
		for (int j = 0; j < featureArray.length; j++) {
			featureMap.put(featureArray[j], j);
		}
	}

	public void implies(String implyFeature, String impliedFeature) {
		implies(implyFeature, impliedFeature, 0);
	}

	public void implies(String implyFeature, String impliedFeature, int negation) {
		switch (negation) {
		case 0:
			setEdge(implyFeature, impliedFeature, ListFeatureGraph.EDGE_11);
			setEdge(impliedFeature, implyFeature, ListFeatureGraph.EDGE_00);
			break;
		case 1:
			setEdge(implyFeature, impliedFeature, ListFeatureGraph.EDGE_10);
			setEdge(impliedFeature, implyFeature, ListFeatureGraph.EDGE_10);
			break;
		case 2:
			setEdge(implyFeature, impliedFeature, ListFeatureGraph.EDGE_01);
			setEdge(impliedFeature, implyFeature, ListFeatureGraph.EDGE_01);
			break;
		case 3:
			setEdge(impliedFeature, implyFeature, ListFeatureGraph.EDGE_11);
			setEdge(implyFeature, impliedFeature, ListFeatureGraph.EDGE_00);
			break;
		}
	}

	public void setEdge(String from, String to, byte edgeType) {
		setEdge(featureMap.get(from), featureMap.get(to), edgeType);
	}

	public int getFeatureIndex(String featureName) {
		final Integer index = featureMap.get(featureName);
		return index != null ? index : -1;
	}

	public int getSize() {
		return size;
	}

	public ArrayList<LinkedList<Expression>> getExpListAr() {
		return expListAr;
	}

	public String[] getFeatureArray() {
		return featureArray;
	}

	public String[] getCoreFeatures() {
		return coreFeatures;
	}

	public String[] getDeadFeatures() {
		return deadFeatures;
	}

}