/**
 * 
 */
package de.ovgu.featureide.core.mpl.job;

import java.util.EventListener;

/**
 * Can be implemented by all classes which are waiting for the end of job sequence to do something.
 * 
 * @author Sebastian Krieter
 * 
 * @see JobManager
 */
public interface SequenceFinishedListener extends EventListener {
	void sequenceFinished(Object idObject, boolean success);
}
