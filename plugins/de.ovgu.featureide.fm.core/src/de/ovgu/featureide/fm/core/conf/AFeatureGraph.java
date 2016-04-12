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

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;

public abstract class AFeatureGraph implements IFeatureGraph {

	private static final long serialVersionUID = 1L;

	public static final byte EDGE_NONE = 0b00000000, //0x00;
			EDGE_00 = 0b00000010, //0x02,
			EDGE_00Q = 0b00000001, //0x01,
			EDGE_01 = 0b00001000, //0x08,
			EDGE_01Q = 0b00000100, //0x04,
			EDGE_10 = 0b00100000, //0x20,
			EDGE_10Q = 0b00010000, //0x10,
			EDGE_11 = (byte) 0b10000000, //0x80,
			EDGE_11Q = 0b01000000, //0x40,

			VALUE_NONE = EDGE_NONE, VALUE_0Q = EDGE_00Q, VALUE_0 = EDGE_00, VALUE_1Q = EDGE_01Q, VALUE_1 = EDGE_01, VALUE_10Q = EDGE_00Q | EDGE_01Q;

	public static final byte MASK_0_CLEAR = (byte) 0b11110000, //0xf3,
			MASK_1_CLEAR = (byte) 0b00001111; //0xf3,

	protected String[] featureArray;
	protected String[] coreFeatures;
	protected String[] deadFeatures;

	protected int size;
	protected HashMap<String, Integer> featureMap;
	protected ArrayList<LinkedList<Expression>> expListAr;
	
	protected final transient IFeatureModel featureModel;

	public static boolean isEdge(byte edge, byte q) {
		return (edge & q) != EDGE_NONE;
	}

	public AFeatureGraph(IFeatureModel featureModel, Collection<IFeature> variantfeatures, Collection<IFeature> coreFeatures, Collection<IFeature> deadFeatures) {
		this.featureModel = featureModel;
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
		for (IFeature feature : coreFeatures) {
			this.coreFeatures[i++] = feature.getName();
		}

		i = 0;
		for (IFeature feature : deadFeatures) {
			this.deadFeatures[i++] = feature.getName();
		}

		i = 0;
		for (IFeature feature : variantfeatures) {
			featureArray[i++] = feature.getName();
		}

		Arrays.sort(featureArray);
		Arrays.sort(this.coreFeatures);
		Arrays.sort(this.deadFeatures);
		for (int j = 0; j < featureArray.length; j++) {
			featureMap.put(featureArray[j], j);
		}
	}
	
	public AFeatureGraph(IFeatureModel featureModel) {
		this.featureModel = featureModel;
	}
	
	public void copyValues(IFeatureGraph otherGraph) {
		final AFeatureGraph anotherAGraph = (AFeatureGraph) otherGraph;
		this.size = anotherAGraph.size;
		this.coreFeatures = Arrays.copyOf(anotherAGraph.coreFeatures, anotherAGraph.coreFeatures.length);
		this.deadFeatures = Arrays.copyOf(anotherAGraph.deadFeatures, anotherAGraph.deadFeatures.length);
		this.featureArray = Arrays.copyOf(anotherAGraph.featureArray, anotherAGraph.featureArray.length);
		this.expListAr = new ArrayList<>(anotherAGraph.expListAr);
		this.featureMap = new HashMap<>(anotherAGraph.featureMap);
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