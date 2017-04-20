//#if CallButtons
package de.ovgu.featureide.examples.elevator.core.controller;

/**
 * This interface represents the main point of interaction with the controller
 * and view. To receive any floor request you have to implement this interface.
 */
public interface ITriggerListener {
	/**
	 * This methods gets called if a trigger is fired. For example if any floor
	 * request is triggered.
	 * 
	 * @param request
	 *            The floor request that is triggered.
	 */
	void trigger(Request request);
	
	//#if Sabbath
//@	void removeMe();
	//#endif

}
//#endif
