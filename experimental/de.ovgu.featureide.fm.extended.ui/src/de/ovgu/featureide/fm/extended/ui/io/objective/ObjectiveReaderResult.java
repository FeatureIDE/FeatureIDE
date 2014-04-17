package de.ovgu.featureide.fm.extended.ui.io.objective;

import de.ovgu.featureide.fm.extended.ui.io.ReaderProblem;
import de.ovgu.featureide.fm.extended.ui.io.constraint.WeightedTerm;

import java.util.Collections;
import java.util.List;

public class ObjectiveReaderResult {

	private List<ReaderProblem> problems;
	
	private List<WeightedTerm> objective;

	public ObjectiveReaderResult(List<ReaderProblem> problems, List<WeightedTerm> objective) {
		this.problems = Collections.unmodifiableList(problems);
		if (objective != null) {
			this.objective = Collections.unmodifiableList(objective);
		}
	}
	
	public List<ReaderProblem> getProblems() {
		return problems;
	}

	public List<WeightedTerm> getObjective() {
		return objective;
	}
	
}
