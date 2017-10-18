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
package org.prop4j.solver;

import org.sat4j.minisat.core.Heap;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.specs.ISolver;

/**
 * Modified variable order for {@link ISolver}.</br> Initializes the used heap in a certain order.
 *
 * @author Sebastian Krieter
 */
public class VarOrderHeap2 extends VarOrderHeap {

	private static final long serialVersionUID = 1L;
	private int[] order;

	public VarOrderHeap2(IPhaseSelectionStrategy strategy, int[] order) {
		super(strategy);
		this.order = order;
	}

	@Override
	public void init() {
		int nlength = lits.nVars() + 1;
		if ((activity == null) || (activity.length < nlength)) {
			activity = new double[nlength];
		}
		phaseStrategy.init(nlength);
		activity[0] = -1;
		heap = new Heap(activity);
		heap.setBounds(nlength);
		nlength--;
		for (int i = 0; i < nlength; i++) {
			final int x = order[i];
			activity[x] = 0.0;
			if (lits.belongsToPool(x)) {
				heap.insert(x);
			}
		}
	}

	public int[] getOrder() {
		return order;
	}

	public void setOrder(int[] order) {
		this.order = order;
	}

}
