/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.deltaj.ui.wizard;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * @author Andr� Specht
 * Adapted for FeatureIDE by Sven Schuster
 */
public class DeltaJFeatureMapper {

	private FeatureModel model;

	public DeltaJFeatureMapper(FeatureModel model){
		this.model = model;
	}
	
	public FeatureModel getModel() {
		return model;
	}

	public void setModel(FeatureModel model) {
		this.model = model;
	}

	public Collection<Feature> getFeatures(){
		return getModel().getFeatures();
	}

	public String getSPLConfiguration(){
		return "configurations "+getConfigurationString(getModel().getRoot());
	}

	public LinkedList<Feature> getMandatoryChildren(Feature f){
		LinkedList<Feature> mands = new LinkedList<Feature>();
		if(f.hasChildren())
			for (Feature feat : f.getChildren()) {
				if(feat.isMandatory()&&!feat.isHidden())
					mands.add(feat);
			}
		return mands;
	}

	public ArrayList<Feature> getEndFeatures(){
		ArrayList<Feature> featurelist = new ArrayList<Feature>();
		Collection<Feature> feats = getModel().getFeatures();
		for (Feature feature : feats) {
			if (!feature.hasChildren()&&!feature.getParent().isHidden()) {
				featurelist.add(feature);
			}
		}
		return featurelist;
	}

	public ArrayList<Feature> getOptionalEndFeatures(){
		ArrayList<Feature> featurelist = new ArrayList<Feature>();
		Collection<Feature> feats = getModel().getFeatures();
		for (Feature feature : feats) {
			if (!feature.hasChildren() && !feature.getParent().isHidden()&&!feature.isMandatory()) {
				featurelist.add(feature);
			}
		}
		return featurelist;
	}

	public ArrayList<Feature> getMandatoryEndFeatures(){
		ArrayList<Feature> featurelist = new ArrayList<Feature>();
		Collection<Feature> feats = getModel().getFeatures();
		for (Feature feature : feats) {
			if (!feature.hasChildren()&&!feature.getParent().isHidden()&&feature.isMandatory()&&allMandatoryBranches(feature)) {
				featurelist.add(feature);
			}
		}
		return featurelist;
	}

	public boolean allMandatoryBranches(Feature feature){
		if(feature.isRoot())
			return true;
		else
			if(!feature.getParent().isMandatory())
				return false;
			else
				return allMandatoryBranches(feature.getParent());
	}



	public String getEndFeatureString(){
		String result = "features ";
		for (Feature feat : getEndFeatures()) {
			if(feat!= getEndFeatures().get(getEndFeatures().size()-1))
				result += feat.getName()+",";
			else
				result += feat.getName();
		}
		return result;
	}


	private String getConfigurationString(Feature feature){
		String result="";

		if(feature.hasChildren()&&!feature.isHidden()){
			if(feature.isAnd()){
				for (Feature f : feature.getChildren()) {
					if(f.isMandatory()&&!f.isHidden()){

						if(result!="")
							result+= " && ("+getConfigurationString(f)+")";
						else
							result+= "("+getConfigurationString(f)+")";
					}

				}
			}

			if(feature.isOr()){
				for (Feature f2 : feature.getChildren()) {
					if(!f2.isHidden()){
						if(result!="")
							result+= " || ("+getConfigurationString(f2)+")";
						else
							result+= " ("+getConfigurationString(f2)+")";
					}
				}
			}


			if(feature.isAlternative()){
				for (Feature f3 : feature.getChildren()) {
					if(!f3.isHidden()){
						if(result!="")
							result+="|| ("+getConfigurationString(f3)+ "&&" +processAltFeature(f3)+")";
						else
							result+=" ("+getConfigurationString(f3)+ "&&" +processAltFeature(f3)+")";
					}
				}

			}
		}
		else
			if(feature.isMandatory()&&!feature.isHidden())
				result+=feature.getName();
		result = result.replaceAll(" && \\(\\)", "");
		return result;
	}

	private String createDelta(Feature deltaFeature){
		String result="delta D"+deltaFeature.getName()+" {\n\t\n}";
		return result;
	}

	private String createCombinedDelta(DOptFeature feature	){
		String result="delta "+feature.getDeltaModule()+" {\n\t\n}";
		return result;
	}

	private String createAllCombinedDeltas(ArrayList<DOptFeature> comb){
		String result = "";
		for (DOptFeature c : comb) {
			result+=createCombinedDelta(c);
		}
		return result;
	}


	private String createAllDeltas(ArrayList<Feature> allFeatureDeltas){
		String result = "";
		for (Feature feature : allFeatureDeltas) {
			result+=createDelta(feature);
		}
		return result;
	}


	private String createRule(Feature feature){
		String prop = getPropForFeature(feature);
		if(!prop.equals(""))
			return "D"+feature.getName()+" when "+getPropForFeature(feature)+"";
		else
			return "D"+feature.getName()+"";
	}

	private String createCombinedRule(DOptFeature comb){
		return comb.getDeltaModule()+" when "+comb.getProp();
	}

	private String createAllRules(ArrayList<Feature> features){
		String result ="";
		for (Feature feature : features) {
			if(feature != features.get(features.size()-1))
				result += "\t"+createRule(feature)+",\n";
			else
				result += "\t"+createRule(feature);
		}
		return result;
	}

	private String createAllCombinedRules(ArrayList<DOptFeature> combinedOptional){
		String result ="";
		for (DOptFeature combs : combinedOptional) {
			if(combs != combinedOptional.get(combinedOptional.size()-1))
				result += "\t"+createCombinedRule(combs)+",\n";
			else
				result += "\t"+createCombinedRule(combs);
		}
		return result;
	}

	private String writeInitialPartition(ArrayList<Feature> optional, ArrayList<DOptFeature> combinedOptional){
		String result="[\n";
		ArrayList<Feature> mEndFeat = getMandatoryEndFeatures();
		if(!mEndFeat.isEmpty()) { 
			result +=createAllRules(mEndFeat);
			if(!optional.isEmpty())
				result+=",\n";
		}
		if(!optional.isEmpty()) {
			result+=createAllRules(optional);
			if(!combinedOptional.isEmpty())
				result+=",\n";
		}
		if(!combinedOptional.isEmpty()) {
			result+=createAllCombinedRules(combinedOptional);
		}
		result+="]\n";
		return result;
	}

	private String createSPL(ArrayList<Feature> optionalSelected,ArrayList<DOptFeature> combinedOptional){
		String result = "";
		//		spl "+getModel().getRoot().getName()+"{\n";
		//		result += "\t"+getEndFeatureString()+"\n";
		//		result += "\t"+getSPLConfiguration()+"\n";
		result += "\tdeltas ";
		result +=writeInitialPartition(optionalSelected,combinedOptional);
		//		result += "\t}\n";
		return result;
	}

	private String createProgram(ArrayList<Feature> optionalSelected,ArrayList<DOptFeature> optionalCombined){
		String result = "";
		result+=createAllDeltas(getMandatoryEndFeatures());
		result+=createAllDeltas(optionalSelected);
		result+=createAllCombinedDeltas(optionalCombined);
		//		result+=createSPL(optionalSelected,optionalCombined);
		return result;
	}

	public String getPropForFeature(Feature feature){
		String result = "";
		if(!feature.isHidden()){
			if(!feature.isRoot()){
				if((!feature.isMandatory()&&!feature.hasChildren())||feature.getParent().isAlternative()||(feature.getParent().isOr()&&!feature.hasChildren()))
					result+=feature.getName();
				if(feature.getParent().isAlternative()){
					if(feature.getParent().isMandatory())
						result+="&& ("+processAltFeature(feature)+") "+getPropForFeature(feature.getParent());
					else
						result+="&& ("+processAltFeature(feature)+") "+getPropForFeature(feature.getParent());
				}
				if(feature.getParent().isAnd()){
					if(feature.getParent().isMandatory())
						result+=""+getPropForFeature(feature.getParent());
					else
						result+=/*" && "*/getPropForFeature(feature.getParent());
				}
				if(feature.getParent().isOr()){
					//					if(feature.getParent().isMandatory())
					result+=""+getPropForFeature(feature.getParent());
					//					else
					//						result+=" && "+getPropForFeature(feature.getParent());
					//
				}

			}
			else {
				result+="";
			}
		}
		return result;
	}

	private String processAltFeature(Feature feature){
		String result ="";
		LinkedList<Feature> featurelist = feature.getParent().getChildren();

		int i = 0;
		for (Feature f : featurelist) {
			if(feature.hasChildren()){
				if(f!= feature){
					if(result.equals("")) {
						result+=processAltFeature(f);
					}
					else {
						result+=" && "+processAltFeature(f);
					}
				}
			}
			else
				if(f!=feature){
					if(i == 0) {
						result+="!"+f.getName();
						i++;
					}
					else {
						result+=" && !"+f.getName();
					}
				}
		}
		return result;
	}

	public ByteArrayOutputStream writeProgram(ArrayList<Feature> optionalSelected,ArrayList<DOptFeature> optionalCombined){
		ByteArrayOutputStream outStream = new ByteArrayOutputStream();
		try {
			outStream.write(createProgram(optionalSelected,optionalCombined).getBytes());
		} catch (IOException e) {
			CorePlugin.getDefault().logError(e);
		}
		return outStream;
	}

	public ByteArrayOutputStream writeSeperateModule(Feature delta){
		ByteArrayOutputStream outStream = new ByteArrayOutputStream();
		try {
			outStream.write(createDelta(delta).getBytes());
		} catch (IOException e) {
			CorePlugin.getDefault().logError(e);
		}
		return outStream;
	}

	public ByteArrayOutputStream writeSeperateCombinedModule(DOptFeature delta){
		ByteArrayOutputStream outStream = new ByteArrayOutputStream();
		try {
			outStream.write(createCombinedDelta(delta).getBytes());
		} catch (IOException e) {
			CorePlugin.getDefault().logError(e);
		}
		return outStream;
	}

	public ByteArrayOutputStream writeSeperateSpl(ArrayList<Feature> optionalSelected,ArrayList<DOptFeature> optionalCombined){
		ByteArrayOutputStream outStream = new ByteArrayOutputStream();
		try {
			outStream.write(createSPL(optionalSelected,optionalCombined).getBytes());
		} catch (IOException e) {
			CorePlugin.getDefault().logError(e);
		}
		return outStream;
	}
}
