package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collection;
import java.util.Set;

/**
 * The PBSolver interface encapsulates the functionality of a pseudo boolean
 * satisfiability solver. Each class that implements this interface can 
 * be plugged in to reason on extended feature models.
 * 
 * @author Sebastian Henneberg
 */
public interface PBSolver {

	/**
	 * Adds a restriction to the pseudo boolean satisfiability solver.
	 * 
	 * @param <T> The concrete type of the restriction.
	 * @param restriction The restriction to add.
	 */
	public <T extends Restriction> void addRestriction(T restriction);
	
	/**
	 * Adds restrictions to the pseudo boolean satisfiability solver.
	 * 
	 * @param <T> The concrete type of the restrictions.
	 * @param restrictions The restrictions to add.
	 */
	public <T extends Restriction> void addRestrictions(
			Collection<T> restrictions);
	
	/**
	 * Is the currently submitted set of restrictions satisfiable?
	 * 
	 * @return True if there is at least one satisfying assignments, false 
	 * otherwise.
	 */
	public boolean isSatisfiable();
	
	/**
	 * Is the currently submitted set of restrictions satisfiable with respect 
	 * of the passed assumptions?
	 * 
	 * @param assumptions An array of temporary assumption used for this call.
	 * @return True if there is at least one satisfying assignments, false 
	 * otherwise.
	 */
	public boolean isSatisfiable(int[] assumptions);
	
	/**
	 * Verifies if the passed variables are either true or false for all 
	 * satisfying assignments. Returns +id for each true assignments and 
	 * -id for each false assignment in the resulting set. In general, the 
	 * resulting set contains fewer elements than the input set because some 
	 * variables are not yet statically assigned.
	 * 
	 * @param varibales The indices of the variables to examine.
	 * @return Those variables that are statically assigned and their assignment. 
	 */
	public Set<Integer> backbone(Set<Integer> varibales);
}
