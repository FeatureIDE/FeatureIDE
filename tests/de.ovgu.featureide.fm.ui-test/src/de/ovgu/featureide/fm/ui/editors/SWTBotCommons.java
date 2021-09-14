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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.EditPart;
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
import org.hamcrest.BaseMatcher;
import org.hamcrest.Description;
import org.prop4j.NodeReader;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ChangeFeatureGroupTypeOperation;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintView;

/**
 * Common static methods for SWTBot tests.
 *
 * @author Kevin Jedelhauser
 * @author Benedikt Jutz
 */
public class SWTBotCommons {

	/**
	 * @author Kevin Jedelhauser
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
				bot.button("No").click();
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

	public static IConstraint extractConstraint(SWTBotGefEditPart constraintEditPart) {
		return ((ConstraintEditPart) constraintEditPart.part()).getModel().getObject();
	}

	/**
	 * @param editor
	 * @param featureName
	 * @param parentPart
	 */
	public static SWTBotGefEditPart createFeatureBelow(SWTBotGefEditor editor, String featureName, SWTBotGefEditPart parentPart) {
		editor.select(parentPart);
		editor.clickContextMenu(StringTable.CREATE_FEATURE_BELOW + " (Ins)");
		final SWTBotGefEditPart newEditPart = editor.getEditPart(StringTable.DEFAULT_FEATURE_LAYER_CAPTION);
		renameFeature(editor, newEditPart, featureName);
		checkParentChildRelation(parentPart, newEditPart);
		return getFeaturePart(editor, featureName);
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

	/**
	 * @param editor - {@link SWTBotGefEditor}
	 * @param formula - {@link String}
	 * @return {@link SWTBotGefEditPart}
	 */
	public static SWTBotGefEditPart createConstraint(SWTBotGefEditor editor, String formula) {
		return openConstraintDialog(editor, "", formula);
	}

	/**
	 * Opens the constraint dialog for the given model <code>editor</code> and rewrites <code>oldFormula</code> to <code>newFormula</code>. Tests if there
	 * exists a new {@link ConstraintEditPart} with <code>newFormula</code> afterwards. If <code>oldFormula</code> is empty, creates a new constraint instead.
	 *
	 * @param editor - {@link SWTBotGefEditor}
	 * @param oldFormula - {@link String}
	 * @param newFormula - {@link String}
	 * @return new {@link SWTBotGefEditPart}
	 */
	public static SWTBotGefEditPart openConstraintDialog(SWTBotGefEditor editor, String oldFormula, String newFormula) {
		if (oldFormula.equals("")) {
			editor.click(1, 1);
			editor.clickContextMenu(StringTable.CREATE_CONSTRAINT);
		} else {
			getConstraintPart(editor, oldFormula).select();
			editor.clickContextMenu(StringTable.EDIT_CONSTRAINT);
		}

		final SWTBotShell sh = editor.bot().shell(StringTable.CONSTRAINT_DIALOG);
		sh.activate();

		if (oldFormula.equals("")) {
			sh.bot().styledText(1).setText(newFormula);
			sh.bot().button(StringTable.CREATE_CONSTRAINT).click();
		} else {
			sh.bot().styledText(oldFormula, 0).setText(newFormula);
			sh.bot().button(StringTable.UPDATE_CONSTRAINT).click();
		}

		return getConstraintPart(editor, newFormula);
	}

	/**
	 * @param editor - {@link SWTBotGefEditor}
	 * @param formula - {@link String}
	 * @return {@link SWTBotGefEditPart}
	 */
	public static SWTBotGefEditPart getConstraintPart(SWTBotGefEditor editor, final String formula) {
		editor.setFocus();
		@SuppressWarnings("unchecked")
		final List<SWTBotGefEditPart> matchingParts = editor.editParts(new BaseMatcher<EditPart>() {

			@Override
			public boolean matches(Object item) {
				if (!(item instanceof ConstraintEditPart)) {
					return false;
				}
				final ConstraintEditPart consPart = (ConstraintEditPart) item;
				final IConstraint cons = consPart.getModel().getObject();
				return cons.getNode().toString(NodeWriter.textualSymbols).equals(formula);
			}

			@Override
			public void describeTo(Description description) {}
		});

		if (matchingParts.isEmpty()) {
			fail("Did not find a suitable ConstraintEditPart!");
		}
		return matchingParts.get(0);
	}

	public static SWTBotGefEditPart prependModelName(SWTBotGefEditor editor, String modelName, String formula) {
		final String[] formulaParts = formula.split(" ");

		final List<String> symbols = Arrays.asList(NodeWriter.textualSymbols);

		for (int iS = 0; iS < formulaParts.length; iS++) {
			if (!symbols.contains(formulaParts[iS])) {
				formulaParts[iS] = modelName + "." + formulaParts[iS];
			}
		}
		final String newFormula = String.join(" ", formulaParts);

		return getConstraintPart(editor, newFormula);
	}

	/**
	 * @param formula
	 * @return
	 */
	public static String getDisplayedFormula(String formula) {
		return new NodeReader().stringToNode(formula).toString(NodeWriter.logicalSymbols);
	}

	/**
	 * @param editor
	 * @param constraintPart
	 */
	public static void deleteConstraint(SWTBotGefEditor editor, SWTBotGefEditPart constraintPart) {
		editor.setFocus();
		constraintPart.select();
		final IConstraint constraint = extractConstraint(constraintPart);
		editor.clickContextMenu(StringTable.DELETE_SHORTCUT);
		assertEquals(-1, constraint.getFeatureModel().getConstraintIndex(constraint));
	}

	/**
	 * @param editor
	 * @param featurePart
	 */
	public static void deleteFeature(SWTBotGefEditor editor, SWTBotGefEditPart featurePart) {
		featurePart.select();
		final IFeature feature = extractFeature(featurePart);
		editor.clickContextMenu(StringTable.DELETE_SHORTCUT);

		assertFalse(feature.getFeatureModel().getFeatures().contains(feature));
	}

	/**
	 * @param editor
	 * @param featurePart
	 * @param allowWithSlicing
	 * @param allowWithoutSlicing
	 */
	public static IFeatureModel checkDeleteWithSlicingOptions(SWTBotGefEditor editor, SWTBotGefEditPart featurePart, boolean allowWithSlicing,
			boolean allowWithoutSlicing) {
		// Select feature part, and click "Delete (Del)" context menu entry.
		featurePart.select();
		editor.clickContextMenu(StringTable.DELETE_SHORTCUT);
		// Get the dialog named "Delete Warning". (see openConstraintDialog)
		final SWTBotShell sh = editor.bot().shell(StringTable.DELETE_WARNING).activate();
		final SWTBot bot = sh.bot();
		// If allowWithSlicing = true, check for "Delete With Slicing" option button existence.
		if (allowWithSlicing) {
			bot.button(StringTable.DELETE_WITH_SLICING).click();
		}
		// If allowWithoutSlicing = true, check for "Delete Without Slicing" option button existence.
		else if (allowWithoutSlicing) {
			bot.button(StringTable.DELETE_WITHOUT_SLICING).isVisible();
		}
		// Check for "Cancel" button, then click it.
		else {
			bot.button(StringTable.CANCEL).click();
		}
		// Return the feature model the feature that featurePart represents belongs to.
		return extractFeature(featurePart).getFeatureModel();
	}

	/**
	 * Returns the position of a {@link FeatureEditPart} stored in featurePart.
	 *
	 * @param featurePart - {@link SWTBotGefEditPart}
	 * @return {@link Point}
	 */
	public static Point extractPosition(SWTBotGefEditPart featurePart) {
		return ((GraphicalFeature) featurePart.part().getModel()).getLocation();
	}

	/**
	 * @param editor
	 * @param featurePart
	 * @param newParentPart
	 * @param automaticLayout
	 */
	public static void moveBelow(SWTBotGefEditor editor, SWTBotGefEditPart featurePart, SWTBotGefEditPart newParentPart, boolean automaticLayout) {
		final Point oldPos = extractPosition(featurePart);
		final Point newPos = extractPosition(newParentPart);

		final IFeature feature = extractFeature(featurePart);
		final IFeature oldParent = feature.getStructure().getParent().getFeature();

		featurePart.select();
		editor.drag(featurePart, newPos.x, newPos.y + 100);
		editor.bot().waitUntil(new DefaultCondition() {

			@Override
			public boolean test() throws Exception {
				return !extractPosition(featurePart).equals(oldPos);
			}

			@Override
			public String getFailureMessage() {
				return "Feature was not moved in time.";
			}
		}, 50);
		if (automaticLayout) {
			checkParentChildRelation(newParentPart, featurePart);
			assertEquals(-1, oldParent.getStructure().getChildIndex(feature.getStructure()));
		} else {
			checkParentChildRelation(getFeaturePart(editor, oldParent.getName()), featurePart);
			assertNotEquals(-1, oldParent.getStructure().getChildIndex(feature.getStructure()));
		}
	}

	/**
	 * Extracts the children features from the feature structure of <code>feature</code>.
	 *
	 * @param feature - {@link IFeature}
	 * @return {@link List}
	 */
	public static List<IFeature> getChildrenFeatures(IFeature feature) {
		return new ArrayList<IFeature>(feature.getStructure().getChildren().stream().map(struct -> struct.getFeature()).toList());
	}
}
