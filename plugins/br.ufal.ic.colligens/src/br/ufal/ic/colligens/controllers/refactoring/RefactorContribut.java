package br.ufal.ic.colligens.controllers.refactoring;

import java.util.Map;

import org.eclipse.ltk.core.refactoring.RefactoringContribution;
import org.eclipse.ltk.core.refactoring.RefactoringDescriptor;

public class RefactorContribut extends RefactoringContribution {

	@SuppressWarnings("rawtypes")
	@Override
	public RefactoringDescriptor createDescriptor(String id, String project, String description, String comment, Map arguments, int flags)
			throws IllegalArgumentException {
		return null;
	}

}
