/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.constraint.analysis;

import static java.lang.String.format;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.sat4j.specs.TimeoutException;

import com.google.common.collect.BiMap;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.velvet.VelvetFeatureModelReader;

/**
 * Checks the {@link ExtendedFeatureModel} for validation.
 * 
 * @author Sebastian Krieter
 */
public class ExtendedFeatureModelAnalyzer extends FeatureModelAnalyzer  {

	private ExtendedFeatureModel efm;
	private BiMap<String, Integer> map;
	private List<DeRestriction> deFm;
	private IProject project;
	
	private UniqueId idGen;
	private RestrictionFactory<DeRestriction> deFactory;

	public ExtendedFeatureModelAnalyzer(ExtendedFeatureModel fm, IProject project) {
		super(fm);
		
		this.project = project;

		this.efm = fm;
		this.idGen = new UniqueId();
		this.map = Translator.buildFeatureNameMap(efm, idGen);
		this.deFactory = new DeRestrictionFactory();
	}
	
	@Override
	public boolean isValid() throws TimeoutException {		
		if (deFm == null)
			setUpDeRestrictions();
		
		PBSolver solver = new SAT4JPBSolver();
		solver.addRestrictions(deFm);
		
		if (!solver.isSatisfiable()) {
			return false;
		}
		
		if (!matchExternals()) {
			return false;
		}
		
		return true;
//		return solver.isSatisfiable();
	}
	
	private boolean matchExternals() {
		// check interfaces
		
		if (null != efm.implementsInterface()){
			// we have an interface and need to check if all interface 
			// features are present in the shadow model.
			for (Feature child : efm.getRoot().getChildren()) {
				if (!checkNodes(child, efm.getShadowModel().getRoot().getChildren())) {
					return false;
				}
			}
		}
		
		if (efm.hasParameters()) {
			// check if parameter models are contained in the shadowmodel at the correct position
			for (String key : efm.getParameters().keySet()){
				String interfaceName = efm.getParameters().get(key);
				String modelName = efm.getInstanceMappings().get(key);

				final ExtendedFeatureModel implementor = new ExtendedFeatureModel();
				final VelvetFeatureModelReader implementorReader = new VelvetFeatureModelReader(implementor);
				final IResource res = project.findMember(format("MPL/%s.velvet", modelName));
				final File file = res.getLocation().toFile();

				try {
					implementorReader.readFromFile(file);
					final ExtendedFeatureModelAnalyzer analyzer = new ExtendedFeatureModelAnalyzer(implementor, project);
					
					if (!(interfaceName.equals(implementor.implementsInterface()) &&
							analyzer.isValid())) {
						return false;
					}
				} catch ( final FileNotFoundException e ) {
					FMCorePlugin.getDefault().logError(e);
				} catch ( final UnsupportedModelException e ) {
					FMCorePlugin.getDefault().logError(e);
				} catch ( TimeoutException e ) {
					FMCorePlugin.getDefault().logError(e);
				}
			}
		}
		return true;
	}
	
	private boolean checkNodes (final Feature curNode, final List<Feature> childrenInShadowModel) {
		for (Feature child : childrenInShadowModel) {
			// check if the two nodes have the same modifiers
			
			// TODO check all modifiers. Currently disabled because Christoph doesn't copy 
			// feature modifiers into the interface
//			if (curNode.isAbstract() && child.isAbstract() &&
//				curNode.isAlternative() && child.isAlternative() &&
//				curNode.isAnd() && child.isAnd() &&
//				curNode.isANDPossible() && child.isANDPossible() &&
//				curNode.isOr() && child.isOr() &&
//				curNode.isMandatory() && child.isMandatory() &&
			if (curNode.getName().equals(child.getName())) {
					// we found a matching feature, now we need to check if all children of
					// curNode are in the children of the found node.
					for (Feature curNodeChildren : curNode.getChildren()) {
						if (!checkNodes(curNodeChildren, child.getChildren())) {
							// a feature was not found.
							return false;
						}
					}
					
					return true;
			}
		}
		
		return false;
	}
	
	private void setUpDeRestrictions() {
		this.deFm = Translator.translateFmTree(map, efm, deFactory);
		this.deFm.addAll(Translator.translateFmConstraints(map, efm, deFactory));
		this.deFm.addAll(Translator.translateEquations(map, efm, 
				efm.getIntegerAttributes(), efm.getAttributConstraints(), deFactory));
	}
}
