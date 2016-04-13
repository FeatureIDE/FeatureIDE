/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
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
