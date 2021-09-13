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
import static org.junit.Assert.fail;

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

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ChangeFeatureGroupTypeOperation;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintView;

/**
 * Common static methods for SWTBot tests.
 *
 * @author Benedikt Jutz
 */
public class SWTBotCommons {

	/**
	 * @author Benedikt Jutz
	 */
	private static final class WaitRenameCondition extends DefaultCondition {

		private final FeatureEditPart featurePart;
		private final String newName;

		/**
		 * @param featurePart
		 * @param newName
		 */
		private WaitRenameCondition(FeatureEditPart featurePart, String newName) {
			this.featurePart = featurePart;
			this.newName = newName;
		}

		@Override
		public boolean test() throws Exception {
			return featurePart.getModel().getObject().getName().equals(newName);
		}

		@Override
		public String getFailureMessage() {
			return "Feature Name didn't change in time.";
		}
	}

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
	public static SWTBotGefEditor openFile(SWTWorkbenchBot bot, SWTBotView projectExplorer, String project, String... fileNames) {
		projectExplorer.setFocus();
		SWTBotTreeItem item = new SWTBot(projectExplorer.getWidget()).tree(0).getTreeItem(project);
		for (final String fileName : fileNames) {
			item = item.expand().getNode(fileName);
		}
		item.doubleClick();

		for (final SWTBotShell shell : bot.shells()) {
			if (shell.getText().equals(StringTable.CONSTRAINT_VIEW_QUESTION_TITLE)) {
				bot.shell(StringTable.CONSTRAINT_VIEW_QUESTION_TITLE).setFocus();
				bot.button("Yes").click();
			}
		}
		return new SWTBotGefEditor(bot.editorByTitle(fileNames[fileNames.length - 1] + " (" + project + ")").getReference(), bot);
	}

	/**
	 * Looks up and returns the feature edit part named <code>name</code> as {@link SWTBotGefEditPart} in <code>editor</code>.
	 *
	 * @param editor - {@link SWTBotGefEditor}
	 * @param name - {@link String}
	 * @return {@link SWTBotGefEditPart}
	 */
	public static SWTBotGefEditPart getFeaturePart(SWTBotGefEditor editor, String name) {
		editor.setFocus();
		final SWTBotGefEditPart editPart = editor.getEditPart(name);
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
		bot.waitUntil(new WaitRenameCondition(featurePart, newName), 100);

		assertEquals(newName, featurePart.getModel().getObject().getName());
	}

	/**
	 * @param editor - {@link SWTBotGefEditor}
	 * @param featureName - {@link String}
	 * @param editParts - {@link SWTBotGefEditPart}
	 */
	public static void createFeatureAbove(SWTBotGefEditor editor, String featureName, SWTBotGefEditPart... editParts) {
		editor.select(editParts);
		editor.clickContextMenu(StringTable.CREATE_FEATURE_ABOVE);
		final SWTBotGefEditPart newFeaturePart = editor.getEditPart(StringTable.DEFAULT_FEATURE_LAYER_CAPTION);
		renameFeature(editor, newFeaturePart, featureName);
		checkParentChildRelation(newFeaturePart, editParts);
	}

	/**
	 * @param parentPart
	 * @param childParts
	 */
	public static void checkParentChildRelation(final SWTBotGefEditPart parentPart, SWTBotGefEditPart... childParts) {
		final IFeature newFeature = extractFeature(parentPart);

		for (final SWTBotGefEditPart editPart : childParts) {
			assertTrue(extractFeature(editPart).getStructure().getParent().getFeature().equals(newFeature));
		}
	}

	public static IFeature extractFeature(SWTBotGefEditPart featureEditPart) {
		return ((FeatureEditPart) featureEditPart.part()).getModel().getObject();
	}

	public static IFeatureStructure extractStructure(SWTBotGefEditPart featureEditPart) {
		return extractFeature(featureEditPart).getStructure();
	}

	/**
	 * @param editor
	 * @param featureName
	 * @param parentPart
	 */
	public static void createFeatureBelow(SWTBotGefEditor editor, String featureName, SWTBotGefEditPart parentPart) {
		editor.select(parentPart);
		editor.clickContextMenu(StringTable.CREATE_FEATURE_BELOW + " (Ins)");
		final SWTBotGefEditPart newEditPart = editor.getEditPart(StringTable.DEFAULT_FEATURE_LAYER_CAPTION);
		renameFeature(editor, newEditPart, featureName);
		checkParentChildRelation(parentPart, newEditPart);
	}

	/**
	 * @param editor
	 * @param string
	 * @param ext4Part
	 */
	public static void createFeatureSibling(SWTBotGefEditor editor, String featureName, SWTBotGefEditPart siblingPart) {
		editor.select(siblingPart);
		editor.clickContextMenu(StringTable.CREATE_SIBLING);
		final SWTBotGefEditPart newEditPart = editor.getEditPart(StringTable.DEFAULT_FEATURE_LAYER_CAPTION);
		renameFeature(editor, newEditPart, featureName);
		final IFeature siblingFeature = extractFeature(siblingPart);
		final SWTBotGefEditPart parentPart = getFeaturePart(editor, siblingFeature.getStructure().getParent().getFeature().getName());
		checkParentChildRelation(parentPart, newEditPart, siblingPart);
	}

	public static void markFeature(SWTBotGefEditor editor, SWTBotGefEditPart featurePart, String property, boolean value) {
		editor.select(featurePart);
		if (!property.equals(StringTable.ABSTRACT_ACTION) && !property.equals(StringTable.MANDATORY_UPPERCASE)) {
			fail("Cannot test property " + property);
		}
		editor.clickContextMenu(property);

		final IFeatureStructure structure = extractStructure(featurePart);
		boolean actualValue;
		if (property.equals(StringTable.ABSTRACT_ACTION)) {
			actualValue = structure.isAbstract();
		} else {
			actualValue = structure.isMandatory();
		}
		assertEquals(value, actualValue);
	}

	/**
	 * @param editor
	 * @param editPart
	 * @param type
	 */
	public static void changeGroupType(SWTBotGefEditor editor, SWTBotGefEditPart editPart, int type) {
		editor.select(editPart);
		String command = null;
		switch (type) {
		case ChangeFeatureGroupTypeOperation.ALTERNATIVE:
			command = StringTable.ALTERNATIVE;
			break;
		case ChangeFeatureGroupTypeOperation.AND:
			command = StringTable.AND;
			break;
		case ChangeFeatureGroupTypeOperation.OR:
			command = StringTable.OR;
			break;
		default:
			fail("No allowed group type specified!");
		}

		editor.clickContextMenu(command);
		final IFeatureStructure structure = extractFeature(editPart).getStructure();

		switch (type) {
		case ChangeFeatureGroupTypeOperation.ALTERNATIVE:
			assertTrue(structure.isAlternative());
			return;
		case ChangeFeatureGroupTypeOperation.AND:
			assertTrue(structure.isAnd());
			return;
		// Default case intercepted previously
		case ChangeFeatureGroupTypeOperation.OR:
		default:
			assertTrue(structure.isOr());
			return;
		}
	}

}
