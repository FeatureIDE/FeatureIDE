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
package de.ovgu.featureide.fm.core.editing;

import java.util.LinkedList;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;

/**
 * Calculates added or deleted products for a feature model edit.
 * 
 * @author Thomas Thuem
 */
public class ExampleCalculator {
	
	private FeatureModel fm;

	private Node a;

	private Node[] bChildren;
	
	private LinkedList<Integer> bSatisfiable;

	private int bIndex;
	
	private SatSolver solver;

	private SatSolver exampleSolver = null;

	private String lastSolution = null;

	private long timeout;
	
	public ExampleCalculator(FeatureModel fm, long timeout) {
		this.fm = fm;
		this.timeout = timeout;
	}

	public void setLeft(Node a) {
		a = a.clone().toCNF();
		this.a = a;
		solver = new SatSolver(a, timeout);
	}

	public void setRight(Node b) {
		b = b.clone().toCNF();
		if (b instanceof Or)
			b = new And(b);
		bChildren = b.getChildren();
		bSatisfiable = new LinkedList<Integer>();
		bIndex = -1;
	}

	public boolean hasNextChild() {
		if(bChildren==null)return false;
		return bIndex + 1 < bChildren.length;
	}

	public Node nextChild() {
		return bChildren[++bIndex];
	}

	public void childIsSatisfiable() {
		bSatisfiable.add(bIndex);
	}
	
	//might return some examples multiple times
	public Configuration nextExample() throws TimeoutException {
		if (exampleSolver == null) {
			if (bSatisfiable.isEmpty() && !findSatisfiable(true))
				return null;
			Node child = bChildren[bSatisfiable.removeFirst()];
			exampleSolver = new SatSolver(new And(a, new Not(child.clone())), timeout);
		}
		String solution = exampleSolver.getSolution();
		if (solution == null) {
			return null;
		}
		if (solution.equals(lastSolution)) {
			exampleSolver = null;
			return nextExample();
		}
		Configuration configuration = new Configuration(fm, false);
		ConfigurationReader reader = new ConfigurationReader(configuration);
		reader.readFromString(solution);
		lastSolution = solution;
		return configuration;
	}

	public boolean findSatisfiable(boolean stopEarly) throws TimeoutException {
		boolean sat = false;
		while (hasNextChild()) {
			Node child = nextChild();
			if (!(child instanceof Or))
				child = new Or(child);
			Node[] list = Node.clone(child.getChildren());
			for (Node node : list)
				((Literal) node).positive ^= true;
			if (solver.isSatisfiable(list)) {
				childIsSatisfiable();
				if (stopEarly)
					return true;
				sat = true;
			}
		}
		return sat;
	}

}
