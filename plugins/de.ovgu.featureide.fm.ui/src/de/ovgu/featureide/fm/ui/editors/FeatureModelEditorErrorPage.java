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
package de.ovgu.featureide.fm.ui.editors;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays a simple error message.
 *
 * @author Sebastian Krieter
 */
public class FeatureModelEditorErrorPage extends FeatureModelEditorPage {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureModelEditorErrorPage";

	private static final String PAGE_TEXT = "Error";

	public FeatureModelEditorErrorPage() {
		super(null, null);
	}

	@Override
	public void createPartControl(Composite parent) {
		final Composite composite = new Composite(parent, SWT.NONE);
		final RowLayout layout = new RowLayout(SWT.HORIZONTAL);
		layout.marginLeft = 10;
		layout.marginTop = 10;
		layout.spacing = 8;
		composite.setLayout(layout);
		final Label imageLabel = new Label(composite, SWT.NONE);
		imageLabel.setImage(FMUIPlugin.getImage("fmerror.png"));
		final Label textLabel = new Label(composite, SWT.NONE);
		final IEditorInput editorInput = getEditorInput();
		if (editorInput instanceof FileEditorInput) {
			textLabel.setText("File <" + editorInput.getName() + "> does not appear to be a feature model!");
		} else {
			textLabel.setText("Input does not appear to be a feature model!");
		}
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	public String getID() {
		return ID;
	}

}
