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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.swt.SWT;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditPart;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.keyboard.Keystrokes;
import org.eclipse.swtbot.swt.finder.waits.DefaultCondition;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;

import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintView;

/**
 * Common static methods for SWTBot tests.
 *
 * @author Benedikt Jutz
 */
public class SWTBotCommons {

	/**
	 * Instructs <code>bot</code> to open the example <code>project</code> as part of the given <code>category</code>.
	 *
	 * @param bot - {@link SWTWorkbenchBot}
	 * @param category - {@link String}
	 * @param part - {@link String}
	 * @param project - {@link String}
	 */
	public static void loadExample(SWTWorkbenchBot bot, String category, String part, String project) {
		bot.menu("File").menu("New").menu("Example...").click();
		bot.shell("New Example").activate();
		bot.text().setText("FeatureIDE Examples");
		bot.button("Next >").click();

		bot.cTabItem(category).activate();
		final SWTBotTreeItem item = bot.tree().getTreeItem(part).expand();
		item.getNode(project).check();
		bot.button("Finish").click();
	}

	/**
	 * Opens a new {@link SWTBotGefEditor} for the given <code>fileName</code> and <code>project</code> in the given view for <code>projectExplorer</code>. Also
	 * dismisses the {@link ConstraintView}, when required.
	 *
	 * @param bot - {@link SWTWorkbenchBot}
	 * @param projectExplorer - {@link SWTBotView}
	 * @param project - {@link String}
	 * @param fileName - {@link String}
	 * @return new {@link SWTBotGefEditor}
	 */
	public static SWTBotGefEditor openFile(SWTWorkbenchBot bot, SWTBotView projectExplorer, String project, String fileName) {
		projectExplorer.setFocus();
		final SWTBotTreeItem projectItem = new SWTBot(projectExplorer.getWidget()).tree(0).getTreeItem(project);
		projectItem.expand().getNode(fileName).doubleClick();

		for (final SWTBotShell shell : bot.shells()) {
			if (shell.getText().equals(StringTable.CONSTRAINT_VIEW_QUESTION_TITLE)) {
				bot.shell(StringTable.CONSTRAINT_VIEW_QUESTION_TITLE).setFocus();
				bot.button("Yes").click();
			}
		}
		return new SWTBotGefEditor(bot.editorByTitle(fileName + " (" + project + ")").getReference(), bot);
	}

	/**
	 * @param osEditor
	 * @param name
	 * @return
	 */
	public static SWTBotGefEditPart getFeaturePart(SWTBotGefEditor osEditor, String name) {
		osEditor.setFocus();
		final SWTBotGefEditPart editPart = osEditor.getEditPart(name);
		assertTrue(editPart.part() instanceof FeatureEditPart);
		return editPart;
	}

	/**
	 * @param editor
	 * @param editPart
	 * @param string
	 */
	public static void renameFeature(SWTBotGefEditor editor, SWTBotGefEditPart editPart, String newName) {
		// TODO Auto-generated method stub
		assertTrue(editPart.part() instanceof FeatureEditPart);
		final FeatureEditPart featurePart = (FeatureEditPart) editPart.part();
		final String oldName = featurePart.getModel().getObject().getName();

		editPart.select();
		editor.clickContextMenu(StringTable.RENAME + " (F2)");
		final SWTBot bot = editor.bot();
		bot.text(oldName).setText(newName).pressShortcut(Keystrokes.create(SWT.CR));
		bot.waitUntil(new DefaultCondition() {

			@Override
			public boolean test() throws Exception {
				return featurePart.getModel().getObject().getName().equals(newName);
			}

			@Override
			public String getFailureMessage() {
				return "Feature Name didn't change in time.";
			}
		}, 100);

		assertEquals(newName, featurePart.getModel().getObject().getName());
	}

}
