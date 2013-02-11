package org.xtext.example.util;

/**
 * Collects the IDE settings for the DJ language features.
 * 
 * @author Fabio
 */
public class DJIdeProperties {
	
	private static ValidationStatus valStatus = ValidationStatus.VALIDATE_ALL;
	
	/**
	 * Change the validation option.
	 * 
	 * @param status the validation option.
	 */
	public static void changeValidationStatus(ValidationStatus status) {
		valStatus = status;
	}
	
	/**
	 * Get the current validation status.
	 * 
	 * @return the current validation status.
	 */
	public static ValidationStatus getValidationStatus() {
		return valStatus;
	}
}
