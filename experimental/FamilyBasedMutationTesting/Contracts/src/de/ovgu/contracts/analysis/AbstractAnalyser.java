package de.ovgu.contracts.analysis;

import java.util.HashMap;
import java.util.Map;

import de.ovgu.contracts.Defaults;

/**
 * 
 * @author Jens Meinicke
 *
 */
public abstract class AbstractAnalyser implements Defaults {

	public Result runRounds() {
		int time = 0;
		boolean foundError = false;
		final String analyser = getName();
		Map<String, String> additions = new HashMap<>();
		for (int i = 0; i < ANALYSIS_ROUNDS; i++) {
			final Result res = run();
			foundError = res.foundError;
			time += res.time;
			additions = res.getAdditions();
		}
		return new Result(analyser, time / ANALYSIS_ROUNDS, foundError, additions);
	}
	
	protected final String getName() {
		return getClass().getSimpleName();
	}

	/**
	 * Executes the Analyser.
	 * @return time for analysis in ms.
	 */
	protected abstract Result run();
}
