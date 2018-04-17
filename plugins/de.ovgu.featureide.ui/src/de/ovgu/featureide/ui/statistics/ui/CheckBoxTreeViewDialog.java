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
package de.ovgu.featureide.ui.statistics.ui;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHOOSE_WHAT_TO_EXPORT;
import static de.ovgu.featureide.fm.core.localization.StringTable.DOUBLE_CLICK_TO_SELECT_ALL_CHILDNODES;
import static de.ovgu.featureide.fm.core.localization.StringTable.INIT_DIALOG___TREEVIEWER;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.ui.statistics.core.ContentProvider;
import de.ovgu.featureide.ui.statistics.core.CsvExporter;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.ui.helper.JobDoneListener;
import de.ovgu.featureide.ui.statistics.ui.helper.TreeLabelProvider;

/**
 * The purpose of this dialog is to display the content of a 'normal' {@link TreeViewer} in a {@link CheckboxTreeViewer} to select some of it's content and then
 * export it to *.csv.
 *
 * @see CsvExporter
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class CheckBoxTreeViewDialog extends Dialog {

	private static final String TOOLTIP = DOUBLE_CLICK_TO_SELECT_ALL_CHILDNODES;
	private static final String TITLE = CHOOSE_WHAT_TO_EXPORT;
	private final Parent invisibleRoot;
	private CheckboxTreeViewer viewer;
	private final TreeViewer oldTree;

	/**
	 * Create the dialog.
	 *
	 * @param parentShell
	 */
	public CheckBoxTreeViewDialog(Shell parentShell, Parent godfather, TreeViewer oldTree) {
		super(parentShell);
		setShellStyle(SWT.DIALOG_TRIM | SWT.MIN | SWT.RESIZE);
		this.oldTree = oldTree;
		invisibleRoot = godfather;
	}

	/**
	 * Create contents of the dialog.
	 *
	 * @param parent
	 */
	@Override
	protected Control createDialogArea(Composite parent) {
		final Composite container = (Composite) super.createDialogArea(parent);
		container.setLayout(new FillLayout(SWT.HORIZONTAL));

		viewer = new CheckboxTreeViewer(container, SWT.BORDER);

		viewer.setContentProvider(new ContentProvider(viewer) {

			@Override
			public Object[] getElements(Object inputElement) {
				if (!(inputElement instanceof Parent)) {
					return getChildren(godfather);
				}
				return getChildren(inputElement);
			}
		});

		viewer.setLabelProvider(new TreeLabelProvider() {

			@Override
			public String getToolTipText(Object element) {
				return TOOLTIP;
			}
		});

		viewer.setInput(invisibleRoot);
		JobDoneListener.getInstance().init(viewer);
		viewer.addCheckStateListener(new CheckBoxListener(viewer));

		initViewer();
		return container;
	}

	/**
	 *
	 */
	private void initViewer() {
		final UIJob job = new UIJob(INIT_DIALOG___TREEVIEWER) {

			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				viewer.setExpandedElements(oldTree.getVisibleExpandedElements());
				viewer.refresh();
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.INTERACTIVE);
		job.schedule();
	}

	@Override
	protected void configureShell(Shell newShell) {
		newShell.setMinimumSize(new Point(300, 400));
		super.configureShell(newShell);
		newShell.setText(TITLE);
		newShell.setImage(GUIDefaults.FEATURE_SYMBOL);
	}

	/**
	 * Create contents of the button bar.
	 *
	 * @param parent
	 */
	@Override
	protected void createButtonsForButtonBar(Composite parent) {
		createButton(parent, IDialogConstants.OK_ID, IDialogConstants.OK_LABEL, true);
		createButton(parent, IDialogConstants.CANCEL_ID, IDialogConstants.CANCEL_LABEL, false);
	}

	@Override
	public boolean close() {
		oldTree.setExpandedElements(viewer.getVisibleExpandedElements());
		return super.close();
	}

	/**
	 * Starts the export.
	 */
	@Override
	protected void okPressed() {
		new CsvExporter(getShell().getParent().getShell()).export(viewer.getCheckedElements());
		super.okPressed();
	}

	/**
	 * Return the initial size of the dialog.
	 */
	@Override
	protected Point getInitialSize() {
		return new Point(600, 500);
	}

}
