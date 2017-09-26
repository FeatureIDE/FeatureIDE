/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.errorpropagation;

import java.util.LinkedList;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;

/**
 * Propagates errors for <code>FeatureHouse</code> C files.
 *
 * @author Jens Meinicke
 */
public class CErrorPropagation extends ErrorPropagation {

	private static final String TASK = "org.eclipse.cdt.core.task";

	protected CErrorPropagation(IFeatureProject featureProject) {
		super(featureProject);
	}

	/**
	 * Sets all composed lines to all methods and fields
	 */
	@Override
	protected void setElementLines(String content, LinkedList<FSTField> fields, LinkedList<FSTMethod> methods) {
		for (final FSTField f : fields) {
			if (f.getBody() == null) {
				continue;
			}
			final int i = content.indexOf(f.getBody());
			if (i == -1) {
				continue;
			}
			final int line = countLines(content.substring(0, i));
			f.setComposedLine(line);
		}

		content = content.replaceAll("__wrappee__\\w*\\s*", "");
		while (content.contains("  ")) {
			content = content.replaceAll("  ", " ");
		}
		content = content.replaceAll("\t", "");
		while (content.contains(" (")) {
			content = content.replaceAll(" \\(", "(");
		}
		while (content.contains(" \n")) {
			content = content.replaceAll(" \n", "\n");
		}

		for (final FSTMethod m : methods) {
			if (m.getBody() == null) {
				continue;
			}
			int i = -1;
			if (m.isConstructor()) {
				String body = m.getBody().substring(m.getBody().indexOf('{') + 1);
				while (body.contains("  ")) {
					body = body.replaceAll("  ", " ");
				}
				body = body.replaceAll("\t", "");
				while (body.contains(" (")) {
					body = body.replaceAll(" \\(", "(");
				}
				body = body.replaceAll("\r\n", "\n");
				while (body.contains(" \n")) {
					body = body.replaceAll(" \n", "\n");
				}
				body = body.substring(0, body.lastIndexOf('}'));
				i = content.indexOf(body);
			} else {
				String body = m.getBody();
				while (body.contains("  ")) {
					body = body.replaceAll("  ", " ");
				}
				body = body.replaceAll("\t", "");
				while (body.contains(" (")) {
					body = body.replaceAll(" \\(", "(");
				}
				body = body.replaceAll("\r\n", "\n");
				while (body.contains(" \n")) {
					body = body.replaceAll(" \n", "\n");
				}
				body = body.replaceAll("original\\(", m.getName() + "(");
				body = body.replaceAll("original\\s*\\(", m.getName() + " (");
				i = content.indexOf(body);
			}
			if (i != -1) {
				final int line = countLines(content.substring(0, i));
				m.setComposedLine(line);
			}
		}
	}

	@Override
	protected boolean propagateMarker(IMarker m) {
		try {
			return !(TASK.equals(m.getType()));
		} catch (final CoreException e) {}
		return super.propagateMarker(m);
	}

}
