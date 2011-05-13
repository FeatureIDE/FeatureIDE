package de.ovgu.featureide.fm.extended.ui.io.constraint;

import de.ovgu.featureide.fm.extended.ui.io.ReaderProblem;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ConstraintReaderResult {

	private List<ReaderProblem> problems = new ArrayList<ReaderProblem>();
	
	private List<Equation> constraints = new ArrayList<Equation>();

	public ConstraintReaderResult(List<ReaderProblem> problems, List<Equation> constraints) {
		this.problems = Collections.unmodifiableList(problems);
		this.constraints = Collections.unmodifiableList(constraints);
	}
	
	public List<ReaderProblem> getProblems() {
		return problems;
	}

	public List<Equation> getConstraints() {
		return constraints;
	}
	
}
