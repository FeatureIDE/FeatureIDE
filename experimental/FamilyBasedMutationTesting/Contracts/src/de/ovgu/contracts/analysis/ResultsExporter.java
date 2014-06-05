package de.ovgu.contracts.analysis;

import java.util.List;

import de.ovgu.contracts.utils.Writer;

/**
 * Exorts the results.
 * @author Jens Meinicke
 *
 */
public class ResultsExporter {

	public final void printResults(final String path, final List<Result> keyResults) {
	    System.out.println("Saving results to: " + path);
		final String content = buildContent(keyResults);
		Writer.setFileContent(path, content);
	}

    private String buildContent(final List<Result> keyResults) {

        final StringBuilder builder = new StringBuilder(keyResults.size() * 2 + 10);
        builder.append("analyser;case-study;mutation size;mutation-type;mutations;error found;time");
        if (!keyResults.isEmpty()) {
            for (final String key : keyResults.get(0).getAdditions().keySet()) {
                builder.append(';');
                builder.append(key);
            }
        }

        for (final Result res : keyResults) {
            builder.append("\r\n");
            builder.append(res);
        }
        return builder.toString();
    }
}
