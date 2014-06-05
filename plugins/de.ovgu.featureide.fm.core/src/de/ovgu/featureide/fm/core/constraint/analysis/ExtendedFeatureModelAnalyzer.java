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

import java.util.List;

import org.sat4j.specs.TimeoutException;

import com.google.common.collect.BiMap;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;

/**
 * Checks the {@link ExtendedFeatureModel} for validation.
 * 
 * @author Sebastian Krieter
 */
public class ExtendedFeatureModelAnalyzer extends FeatureModelAnalyzer  {

	private ExtendedFeatureModel efm;
	private BiMap<String, Integer> map;
	private List<DeRestriction> deFm;
	
	private UniqueId idGen;
	private RestrictionFactory<DeRestriction> deFactory;

	public ExtendedFeatureModelAnalyzer(ExtendedFeatureModel fm) {
		super(fm);

		this.efm = fm;
		this.idGen = new UniqueId();
		this.map = Translator.buildFeatureNameMap(efm, idGen);
		this.deFactory = new DeRestrictionFactory();
	}
	
	public boolean isValid_PBSolver() throws TimeoutException {		
		if (deFm == null)
			setUpDeRestrictions();
		
		PBSolver solver = new SAT4JPBSolver();
		solver.addRestrictions(deFm);
		
		if (!solver.isSatisfiable()) {
			return false;
		}
		
		return true;
	}
	
	private void setUpDeRestrictions() {
		this.deFm = Translator.translateFmTree(map, efm, deFactory);
		this.deFm.addAll(Translator.translateFmConstraints(map, efm, deFactory));
		this.deFm.addAll(Translator.translateEquations(map, efm, 
				efm.getIntegerAttributes(), efm.getAttributConstraints(), deFactory));
	}
}
