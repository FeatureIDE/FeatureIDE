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
package de.ovgu.featureide.fm.core.explanations.fm;

import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel.FeatureModelElementTrace;
import de.ovgu.featureide.fm.core.explanations.Reason;

/**
 * A reason of an explanation involving a feature model.
 *
 * @author Timo G&uuml;nther
 */
public class FeatureModelReason extends Reason {

	/** The trace of this reason. */
	private final FeatureModelElementTrace trace;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param trace the trace of this reason; not null
	 */
	public FeatureModelReason(FeatureModelElementTrace trace) {
		this.trace = trace;
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param reason reason to clone; not null
	 */
	protected FeatureModelReason(FeatureModelReason reason) {
		super(reason);
		trace = reason.trace;
	}

	/**
	 * Returns the trace of this reason.
	 *
	 * @return the trace of this reason; not null
	 */
	public FeatureModelElementTrace getTrace() {
		return trace;
	}

	@Override
	public float getConfidence() {
		/*
		 * TODO Provide a useful explanation count for redundant constraints. The explanation count for redundant constraints is currently useless. To avoid
		 * confusing the user, do not take it into account when giving confidence hints and default to 1.
		 */
		if (getExplanation() instanceof RedundantConstraintExplanation) {
			return 1.0f;
		}
		return super.getConfidence();
	}

	@Override
	protected FeatureModelReason clone() {
		return new FeatureModelReason(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((trace == null) ? 0 : trace.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final FeatureModelReason other = (FeatureModelReason) obj;
		if (trace == null) {
			if (other.trace != null) {
				return false;
			}
		} else if (!trace.equals(other.trace)) {
			return false;
		}
		return true;
	}
}
