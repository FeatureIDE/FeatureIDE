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
package de.ovgu.featureide.fm.core.editing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.impl.FeatureStructure;

/**
 * <p> A trace model for when a {@link IFeatureModel feature model} is transformed into a {@link Node}. </p>
 *
 * <p> When a feature model is transformed into a propositional formula, the mapping between the two formats is ambiguous. For instance, depending on the group
 * type and the amount of children, a child relationship may be mapped to fewer or more clauses than source elements. To solve this, a trace model containing
 * instances of this class can be used to remember the mapping. In particular, using a trace model, the corresponding source {@link IFeatureModelElement
 * element} may be looked up from the target {@link Node formula}. </p>
 *
 * <p> Note, however, that this is not implemented as map from target formula to source element. After all, two clauses that are equal may occur multiple times
 * in the same formula while originating from different source elements. For example, a feature model containing a parent feature <i>P</i>, a child feature
 * <i>C</i> and a constraint <i>C</i> &rArr; <i>P</i>, the target formula would be: <pre>(<i>C</i> &rArr; <i>P</i>) &and; (<i>C</i> &rArr; <i>P</i>)</pre> Both
 * of these two clauses could stem from either the child relationship or the constraint. To differentiate these cases, the lookup is done using the index of the
 * clause in the formula. </p>
 *
 * @author Timo G&uuml;nther
 * @see AdvancedNodeCreator#getTraceModel()
 */
public class FeatureModelToNodeTraceModel implements Cloneable {

	/**
	 * Denotes the origin type of the target clause.
	 *
	 * @author Sofia Ananieva
	 * @author Timo G&uuml;nther
	 */
	public enum Origin {
		/**
		 * <p> Denotes that the clause's origin is a {@link FeatureStructure#getChildren() child feature} directed upward. </p>
		 *
		 * <p> The upward part of the child relationship is that of the following form: <pre><i>Child<sub>1</sub></i> &or; &hellip; &or;
		 * <i>Child<sub>n</sub></i> &rArr; <i>Parent</i></pre> Every child relationship contains an upward part. In fact, optional child relationships consist
		 * of nothing but an upward part (with <i>n</i> = 1). </p>
		 */
		CHILD_UP,
		/**
		 * <p> Denotes that the clause's origin is a {@link FeatureStructure#getChildren() child feature} directed downward. </p>
		 *
		 * <p> The upward part of the child relationship is that of the following form: <pre><i>Parent</i> &rArr; <i>Child<sub>1</sub></i> &or; &hellip; &or;
		 * <i>Child<sub>n</sub></i></pre> Every non-optional child relationship contains a downward part. </p>
		 */
		CHILD_DOWN,
		/**
		 * <p> Denotes that the clause's origin is a {@link FeatureStructure#getChildren() child feature} not directed {@link CHILD_UP upward} or
		 * {@link CHILD_DOWN downward}. </p>
		 *
		 * <p> This is the case for {@link FeatureStructure#isAlternative() alternative groups}, which (in addition to upward and downward parts) contain the
		 * following part: <pre>atmost1(<i>Child<sub>1</sub></i>, &hellip;, <i>Child<sub>n</sub></i>)</pre> </p>
		 */
		CHILD_HORIZONTAL,
		/** Denotes that the literal's origin is the {@link FeatureStructure#isRoot() root feature}. */
		ROOT,
		/** Denotes that the literal's origin is a {@link IConstraint constraint}. */
		CONSTRAINT
	}

	/**
	 * A part of a trace model. Remembers the source elements of a single clause.
	 *
	 * @author Timo G&uuml;nther
	 */
	public static class FeatureModelElementTrace implements Cloneable {

		/** The origin type of the formula. */
		private final Origin origin;
		/** The single source feature model element. */
		private final IFeatureModelElement element;
		/** The multiple source feature model elements. */
		private final Set<IFeatureModelElement> elements;

		/**
		 * Creates a trace for a vertical child relationship.
		 *
		 * @param parent the parent of the relationship; not null
		 * @param children the children of the relationship; not null or empty
		 * @param up true for {@link Origin#CHILD_UP upward child relationship}, false for {@link Origin#CHILD_DOWN downward child relationship}
		 */
		protected FeatureModelElementTrace(IFeature parent, Collection<IFeature> children, boolean up) {
			origin = up ? Origin.CHILD_UP : Origin.CHILD_DOWN;
			element = parent;
			elements = new LinkedHashSet<IFeatureModelElement>(children);
		}

		/**
		 * Creates a trace for a horizontal child relationship.
		 *
		 * @param children the children of the relationship; not null or empty
		 */
		protected FeatureModelElementTrace(Collection<IFeature> children) {
			origin = Origin.CHILD_HORIZONTAL;
			element = null;
			elements = new LinkedHashSet<IFeatureModelElement>(children);
		}

		/**
		 * Creates a trace for the root feature.
		 *
		 * @param root the root feature; not null
		 */
		protected FeatureModelElementTrace(IFeature root) {
			origin = Origin.ROOT;
			element = root;
			elements = null;
		}

		/**
		 * Creates a trace for a constraint.
		 *
		 * @param constraint a constraint; not null
		 */
		protected FeatureModelElementTrace(IConstraint constraint) {
			origin = Origin.CONSTRAINT;
			element = constraint;
			elements = null;
		}

		/**
		 * Creates a new trace. Used in cloning.
		 *
		 * @param origin the origin type of the formula; not null
		 * @param element the single source feature model element
		 * @param elements the multiple source feature model elements
		 */
		private FeatureModelElementTrace(Origin origin, IFeatureModelElement element, Set<IFeatureModelElement> elements) {
			this.origin = origin;
			this.element = element;
			this.elements = elements;
		}

		/**
		 * Returns the containing trace model.
		 *
		 * @return the containing trace model; not null
		 */
		public FeatureModelElementTrace getTraceModel() {
			return FeatureModelElementTrace.this;
		}

		/**
		 * Returns the origin type.
		 *
		 * @return the origin type; not null
		 */
		public Origin getOrigin() {
			return origin;
		}

		/**
		 * Returns the multiple source elements. For a child relationship, this means the children. Otherwise, this means a singleton of the single source
		 * element.
		 *
		 * @return the multiple source elements; not null or empty
		 */
		public Set<IFeatureModelElement> getElements() {
			switch (getOrigin()) {
			case CHILD_UP:
			case CHILD_DOWN:
			case CHILD_HORIZONTAL:
				return elements;
			default:
				return Collections.singleton(element);
			}
		}

		/**
		 * Returns the single source element. For a child relationship, this means the parent. For the root, this means the root. For a constraint, this means
		 * the constraint.
		 *
		 * @return the single source element; null if the origin is a {@link Origin#CHILD_HORIZONTAL horizontal child relationship}
		 */
		public IFeatureModelElement getElement() {
			return element;
		}

		/**
		 * Returns a propositional formula that logically equals the source.
		 *
		 * @return a propositional formula that logically equals the source; not null
		 */
		public Node getNode() {
			switch (getOrigin()) {
			case CHILD_UP:
				return new Implies(new Or(getLiterals()), getLiteral());
			case CHILD_DOWN:
				return new Implies(getLiteral(), new Or(getLiterals()));
			case CHILD_HORIZONTAL:
				return new Not(new And(getLiterals()));
			case ROOT:
				return getLiteral();
			case CONSTRAINT:
				return ((IConstraint) getElement()).getNode();
			default:
				throw new IllegalStateException("Unknown origin");
			}
		}

		/**
		 * Returns literals for the multiple source elements.
		 *
		 * @return literals for the multiple source elements; not null
		 */
		private Node[] getLiterals() {
			final Set<IFeatureModelElement> elements = getElements();
			final Node[] literals = new Node[elements.size()];
			int i = 0;
			for (final IFeatureModelElement element : elements) {
				literals[i++] = getLiteral((IFeature) element);
			}
			return literals;
		}

		/**
		 * Returns a literal for the single source element.
		 *
		 * @return a literal for the single source element; not null
		 */
		private Literal getLiteral() {
			return getLiteral((IFeature) getElement());
		}

		/**
		 * Returns a literal for the given feature.
		 *
		 * @param feature feature to transform; not null
		 * @return a literal for the given feature; not null
		 */
		private Literal getLiteral(IFeature feature) {
			return new Literal(NodeCreator.getVariable(feature));
		}

		@Override
		protected FeatureModelElementTrace clone() {
			return new FeatureModelElementTrace(origin, element, elements);
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = (prime * result) + ((origin == null) ? 0 : origin.hashCode());
			result = (prime * result) + ((element == null) ? 0 : element.hashCode());
			result = (prime * result) + ((elements == null) ? 0 : elements.hashCode());
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
			final FeatureModelElementTrace other = (FeatureModelElementTrace) obj;
			if (origin != other.origin) {
				return false;
			}
			if (element == null) {
				if (other.element != null) {
					return false;
				}
			} else if (!element.equals(other.element)) {
				return false;
			}
			if (elements == null) {
				if (other.elements != null) {
					return false;
				}
			} else if (!elements.equals(other.elements)) {
				return false;
			}
			return true;
		}

		@Override
		public String toString() {
			return toString(NodeWriter.shortSymbols);
		}

		/**
		 * Returns this trace as a string.
		 *
		 * @param symbols symbols to use with {@link NodeWriter}
		 * @return this trace as a string; not null
		 */
		public String toString(String[] symbols) {
			final NodeWriter w = new NodeWriter(getNode());
			w.setSymbols(symbols);
			return w.nodeToString();
		}
	}

	/** The traces of this model. */
	private final List<FeatureModelElementTrace> traces = new ArrayList<>();

	/**
	 * Adds a trace for an {@link Origin#CHILD_UP upward child relationship}.
	 *
	 * @param parent the parent of the relationship; not null
	 * @param children the children of the relationship; not null or empty
	 */
	public void addTraceChildUp(IFeature parent, Collection<IFeature> children) {
		traces.add(new FeatureModelElementTrace(parent, children, true));
	}

	/**
	 * Adds a trace for a {@link Origin#CHILD_DOWN downward child relationship}.
	 *
	 * @param parent parent of the relationship; not null
	 * @param children the children of the relationship; not null or empty
	 */
	public void addTraceChildDown(IFeature parent, Collection<IFeature> children) {
		traces.add(new FeatureModelElementTrace(parent, children, false));
	}

	/**
	 * Adds a trace for a {@link Origin#CHILD_HORIZONTAL horizontal child relationship}.
	 *
	 * @param children the children of the relationship; not null or empty
	 */
	public void addTraceChildHorizontal(Collection<IFeature> children) {
		traces.add(new FeatureModelElementTrace(children));
	}

	/**
	 * Adds a trace for the {@link Origin#ROOT root}.
	 *
	 * @param root the root; not null
	 */
	public void addTraceRoot(IFeature root) {
		traces.add(new FeatureModelElementTrace(root));
	}

	/**
	 * Adds a trace for a {@link Origin#CONSTRAINT}.
	 *
	 * @param constraint a constraint; not null
	 */
	public void addTraceConstraint(IConstraint constraint) {
		traces.add(new FeatureModelElementTrace(constraint));
	}

	/**
	 * Removes the given amount of traces from the end of this trace model.
	 *
	 * @param amount amount of traces to remove
	 */
	public void removeTraces(int amount) {
		int size = getTraceCount();
		while (--amount >= 0) {
			removeTrace(--size);
		}
	}

	/**
	 * Removes the trace for the clause with the given index.
	 *
	 * @param clauseIndex index of the clause to remove
	 */
	public void removeTrace(int clauseIndex) {
		traces.remove(clauseIndex);
	}

	/**
	 * Returns the trace for the clause with the given index.
	 *
	 * @param clauseIndex index of the clause to look up
	 * @return the trace
	 */
	public FeatureModelElementTrace getTrace(int clauseIndex) {
		return traces.get(clauseIndex);
	}

	/**
	 * Returns the amount of traces in this trace model.
	 *
	 * @return the amount of traces in this trace model
	 */
	public int getTraceCount() {
		return traces.size();
	}

	@Override
	protected FeatureModelToNodeTraceModel clone() {
		final FeatureModelToNodeTraceModel clone = new FeatureModelToNodeTraceModel();
		clone.traces.addAll(traces);
		return clone;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((traces == null) ? 0 : traces.hashCode());
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
		final FeatureModelToNodeTraceModel other = (FeatureModelToNodeTraceModel) obj;
		if (traces == null) {
			if (other.traces != null) {
				return false;
			}
		} else if (!traces.equals(other.traces)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName() + " [" + "traces=" + traces + "]";
	}
}
