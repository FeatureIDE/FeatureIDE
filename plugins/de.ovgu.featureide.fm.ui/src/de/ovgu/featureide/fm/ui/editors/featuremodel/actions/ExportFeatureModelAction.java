/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.EXPORT_AS;

import java.util.Arrays;

import org.eclipse.jface.action.Action;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.GraphicsExporter;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;

/**
 *
 *
 *
 * @author Guenter Ulreich
 * @author Andy Koch
 */
public class ExportFeatureModelAction extends Action {

	public static final String ID = "de.ovgu.featureide.exportfeaturemodel";

	private final FeatureDiagramEditor featureModelEditor;

	public ExportFeatureModelAction(FeatureDiagramEditor featureModelEditor) {
		super(EXPORT_AS);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/export_wiz.gif"));
		this.featureModelEditor = featureModelEditor;
		setEnabled(true);
		setId(ID);
	}

	@Override
	public void run() {
		final Shell shell;
		try {
			final IWorkbench workbench = PlatformUI.getWorkbench();
			if (workbench == null) {
				return;
			}
			final IWorkbenchWindow activeWorkbenchWindow = workbench.getActiveWorkbenchWindow();
			if (activeWorkbenchWindow == null) {
				return;
			}
			shell = activeWorkbenchWindow.getShell();
		} catch (final Exception e) {
			return;
		}

		final String[] formats = GraphicsExporter.exporter.stream().map((exporter) -> exporter.getDescription() + "*." + //
			exporter.getFileExtension()).toArray(String[]::new);

		final String defaultPath = featureModelEditor.getFeatureModel().getVarObject().getSourceFile().getParent().toString();
		final ExportFeatureModelDialog dialog = new ExportFeatureModelDialog(shell, defaultPath, formats,
				// format check callback
				(formatIndex) -> new ProblemList(Arrays.asList(new Problem("This format may only be exported.", 0))),
				// export callback
				(formatIndex, path, name) -> GraphicsExporter.exportAs(featureModelEditor.getViewer(),
						path.resolve(name + "." + GraphicsExporter.exporter.get(formatIndex).getFileExtension()).toString(), formatIndex));
		dialog.open();
	}
}
