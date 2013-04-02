package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

/**
 * The different feature model analysis operations need different concrete
 * implementations to reason on the input date. This interface of an abstract 
 * factory enables to use a general translation utility that builds restrictions
 * out of a feature model and additional constraints. 
 * 
 * @author Sebastian Henneberg
 *
 * @param <T> The concrete type of the restriction.
 */
public interface RestrictionFactory<T> {

	/**
	 * Creates a new restriction equivalent but not identical to the arguments. 
	 * 
	 * @param terms Linear term used on the left side of the restriction.
	 * @param op The operator which is either LEQ, EQ or GEQ. 
	 * @param degree The degree is an integer number on the right hand side.
	 * @param restrictions The collection where the new restriction will be stored.
	 * @return An instance representing an equivalent restriction.
	 */
	void createAndAdd(List<Term> terms, RelationOperator op, int degree, 
			Collection<T> restrictions);
	
}
