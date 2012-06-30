/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.featurehouse.errorpropagation;

import java.util.LinkedList;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;

/**
 * Propagates errors for <code>FeatureHouse</code> C files.
 * 
 * @author Jens Meinicke
 */
public class CErrorPropagation extends ErrorPropagation {
	
	private static final String TASK = "org.eclipse.cdt.core.task";

	/**
	 * Sets all composed lines to all methods and fields
	 */
	@Override
	protected void setElementLines(String content, LinkedList<FSTField> fields, LinkedList<FSTMethod> methods) {
		for (FSTField f : fields) {
			if (f.getBody() == null) {
				continue;
			}
			int i = content.indexOf(f.getBody());
			if (i == -1) {
				continue;
			}
			int line = countLines(content.substring(0, i));
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

		for (FSTMethod m : methods) {
			if (m.getBody() == null) {
				continue;
			}
			int i = -1;
			if (m.isConstructor) {
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
				body = body.replaceAll("original\\(", m.getMethodName() + "(");
				body = body.replaceAll("original\\s*\\(", m.getMethodName() + " (");
				i = content.indexOf(body);
			}
			if (i != -1) {
				int line = countLines(content.substring(0, i));
				m.setLine(line);
			}
		}
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.featurehouse.errorpropagation.ErrorPropagation#propagateMarker(org.eclipse.core.resources.IMarker)
	 */
	@Override
	boolean propagateMarker(IMarker m) {
		try {
			return !(TASK.equals(m.getType()));
		} catch (CoreException e) {
		}
		return super.propagateMarker(m);
	}

}
