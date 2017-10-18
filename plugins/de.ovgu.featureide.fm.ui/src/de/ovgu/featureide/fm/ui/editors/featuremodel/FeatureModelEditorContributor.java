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
package de.ovgu.featureide.fm.ui.editors.featuremodel;

import org.eclipse.gef.ui.actions.GEFActionConstants;
import org.eclipse.gef.ui.actions.ZoomComboContributionItem;
import org.eclipse.jface.action.ContributionItem;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.ide.IDEActionFactory;
import org.eclipse.ui.part.EditorActionBarContributor;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AlternativeAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AndAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CalculateDependencyAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateCompoundAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateLayerAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.MandatoryAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.OrAction;

/**
 * Defines the actions for the feature model editor and contributes them.
 *
 * @author Thomas Thuem
 */
public class FeatureModelEditorContributor extends EditorActionBarContributor {

	private static final String[] DIAGRAM_ACTION_IDS = { CreateLayerAction.ID, CreateCompoundAction.ID, CalculateDependencyAction.ID, DeleteAction.ID,
		MandatoryAction.ID, AndAction.ID, OrAction.ID, AlternativeAction.ID, ActionFactory.UNDO.getId(), ActionFactory.REDO.getId(),
		// ActionFactory.CUT.getId(), ActionFactory.COPY.getId(),
		// ActionFactory.PASTE.getId(),
		ActionFactory.SELECT_ALL.getId(),
		// ActionFactory.FIND.getId(),
		ActionFactory.PRINT.getId(), GEFActionConstants.ZOOM_IN, GEFActionConstants.ZOOM_OUT,
			// IDEActionFactory.BOOKMARK.getId()
	};

	private static final String[] TEXTEDITOR_ACTION_IDS = { ActionFactory.DELETE.getId(), ActionFactory.UNDO.getId(), ActionFactory.REDO.getId(),
		ActionFactory.CUT.getId(), ActionFactory.COPY.getId(), ActionFactory.PASTE.getId(), ActionFactory.SELECT_ALL.getId(), ActionFactory.FIND.getId(),
		ActionFactory.PRINT.getId(), IDEActionFactory.BOOKMARK.getId() };

	@Override
	public void setActiveEditor(IEditorPart targetEditor) {
		final FeatureModelEditor editor = (FeatureModelEditor) targetEditor;
		setActivePage(editor, editor.getActivePage());
	}

	public void setActivePage(FeatureModelEditor editor, int pageIndex) {
		final IActionBars actionBars = getActionBars();
		if (actionBars != null) {
			switch (pageIndex) {
			case 0:
				hookGlobalDiagramActions(editor, actionBars);
				break;
			case 1:
				hookGlobalTextActions(editor, actionBars);
				break;
			}
			actionBars.updateActionBars();
		}
	}

	private void hookGlobalDiagramActions(FeatureModelEditor editor, IActionBars actionBars) {
		for (int i = 0; i < DIAGRAM_ACTION_IDS.length; i++) {
			actionBars.setGlobalActionHandler(DIAGRAM_ACTION_IDS[i], editor.getDiagramAction(DIAGRAM_ACTION_IDS[i]));
		}
	}

	private void hookGlobalTextActions(FeatureModelEditor editor, IActionBars actionBars) {
		final ITextEditor textEditor = editor.getSourceEditor();
		for (int i = 0; i < TEXTEDITOR_ACTION_IDS.length; i++) {
			actionBars.setGlobalActionHandler(TEXTEDITOR_ACTION_IDS[i], textEditor.getAction(TEXTEDITOR_ACTION_IDS[i]));
		}
	}

	@Override
	public void contributeToToolBar(IToolBarManager manager) {
		super.contributeToToolBar(manager);
		manager.add(new Separator());

		// Fix for Issue #363
		if (org.eclipse.core.runtime.Platform.getOS().equals(org.eclipse.core.runtime.Platform.OS_WIN32)) {
			manager.add(new ContributionItem() {

				final Point size = new Point(0, 30);
				private ToolItem widget;

				@Override
				public void fill(ToolBar parent, int index) {
					if ((widget == null) && (parent != null)) {
						final int flags = SWT.PUSH;

						ToolItem ti = null;
						if (index >= 0) {
							ti = new ToolItem(parent, flags, index);
						} else {
							ti = new ToolItem(parent, flags);
						}
						ti.setData(this);

						// create an image the height of the text field
						final Image image = new Image(Display.getCurrent(), 1, size.y);
						final GC gc = new GC(image);
						gc.setBackground(parent.getBackground());
						gc.fillRectangle(image.getBounds());
						gc.dispose();
						ti.addDisposeListener(new DisposeListener() {

							@Override
							public void widgetDisposed(DisposeEvent e) {
								image.dispose();
							}
						});
						ti.setImage(image);

						widget = ti;
					}
				}
			});
		}

		manager.add(new ZoomComboContributionItem(getPage()));
	}

}
