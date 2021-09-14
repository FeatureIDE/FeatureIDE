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
import static org.junit.Assert.assertTrue;

import java.util.Collections;
import java.util.List;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditPart;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ChangeFeatureGroupTypeOperation;

/**
 * Tests that the UVL model changes are propagated correctly from submodels. Uses the Universal-Variability-Language-Multi example. Provides (GUI) tests for
 * Issue #1134.
 *
 * @author Kevin Jedelhauser
 * @author Benedikt Jutz
 */
@RunWith(SWTBotJunit4ClassRunner.class)
public class UVLChangeListenersTest {

	/**
	 * The SWTBot to access the IDE with.
	 */
	private static SWTWorkbenchBot bot;
	/**
	 * The editor for the Server model in "Server.uvl".
	 */
	private static SWTBotGefEditor serverEditor;
	/**
	 * Editor for the OperatingSystem model in "OperatingSystem.uvl".
	 */
	private static SWTBotGefEditor osEditor;
	/**
	 * Editor for the FileSystem model in "submodels/FileSystem.uvl".
	 */
	private static SWTBotGefEditor fsEditor;

	/**
	 * For setup, open a new FeatureIDE instance, and then import the Universal-Variability-Language-Multi example. Open all three model files:
	 * submodels/FileSystem.uvl, OperatingSystem.uvl, and Server.uvl. Also use the FeatureIDE perspective.
	 */
	@BeforeClass
	public static void beforeClass() {
		System.setProperty("org.eclipse.swtbot.playback.poll.delay", "50");
		bot = new SWTWorkbenchBot();
		bot.viewByTitle("Welcome").close();

		SWTBotCommons.loadExample(bot, "Feature Modeling", "Universal Variability Language", "Universal-Variability-Language-Multi");
		final SWTBotView projectExplorer = bot.viewByTitle("Project Explorer");
		serverEditor = SWTBotCommons.openFile(bot, projectExplorer, "Universal-Variability-Language-Multi", "Server.uvl");
		osEditor = SWTBotCommons.openFile(bot, projectExplorer, "Universal-Variability-Language-Multi", "OperatingSystem.uvl");
		fsEditor = SWTBotCommons.openFile(bot, projectExplorer, "Universal-Variability-Language-Multi", "submodels", "FileSystem.uvl");
	}

	/**
	 * Test name propagation: <br> Change the name of "Windows" in OperatingSystem to "Windows 10"; assert that the name changes in OperatingSystem and Server.
	 */
	@Test
	public void namePropagationTest() {
		osEditor.show();
		final SWTBotGefEditPart windowsPart = SWTBotCommons.getFeaturePart(osEditor, "Windows");
		SWTBotCommons.renameFeature(osEditor, windowsPart, "Windows_10");
		SWTBotCommons.getFeaturePart(serverEditor, "os.Windows_10");
		bot.menu("Edit").menu("Undo " + StringTable.RENAME_FEATURE).click();

	}

	/**
	 * Test feature creation above: <br> Select features "Debian" and "macOS"; then create a new feature called "Unix" above. Assert these features also appear
	 * with the "os."-alias in the server model.
	 */
	@Test
	public void featureAddAboveTest() {
		osEditor.show();
		final SWTBotGefEditPart macOsPart = SWTBotCommons.getFeaturePart(osEditor, "macOS");
		final SWTBotGefEditPart debianPart = SWTBotCommons.getFeaturePart(osEditor, "Debian");
		SWTBotCommons.createFeatureAbove(osEditor, "Unix", macOsPart, debianPart);

		final SWTBotGefEditPart macOsImport = SWTBotCommons.getFeaturePart(serverEditor, "os.macOS");
		final SWTBotGefEditPart debianImport = SWTBotCommons.getFeaturePart(serverEditor, "os.Debian");
		SWTBotCommons.checkParentChildRelation(SWTBotCommons.getFeaturePart(serverEditor, "os.Unix"), macOsImport, debianImport);
		bot.menu("Edit").menu("Undo " + StringTable.RENAME_FEATURE).click();
		bot.menu("Edit").menu("Undo " + StringTable.CREATE_FEATURE_ABOVE).click();

	}

	/**
	 * Test feature creation below: <br> Create the "Options" feature in FileSystem; assert it to appear as child "fs.Options" of "fs.FileSystem".
	 */
	@Test
	public void featureAddBelowTest() {
		fsEditor.show();
		final SWTBotGefEditPart fileSystemPart = SWTBotCommons.getFeaturePart(fsEditor, "FileSystem");
		SWTBotCommons.createFeatureBelow(fsEditor, "Options", fileSystemPart);

		SWTBotCommons.checkParentChildRelation(SWTBotCommons.getFeaturePart(serverEditor, "fs.FileSystem"),
				SWTBotCommons.getFeaturePart(serverEditor, "fs.Options"));

		bot.menu("Edit").menu("Undo " + StringTable.RENAME_FEATURE).click();
		bot.menu("Edit").menu("Undo " + StringTable.CREATE_FEATURE_BELOW).click();
	}

	/**
	 * Test feature creation as sibling: <br> Create the "ZFS" feature in FileSystem as sibling for "EXT4", assert it to appear alongside "fs.EXT4" in the
	 * Server editor.
	 */
	@Test
	public void featureAddSiblingTest() {
		fsEditor.show();
		final SWTBotGefEditPart ext4Part = SWTBotCommons.getFeaturePart(fsEditor, "EXT4");

		SWTBotCommons.createFeatureSibling(fsEditor, "ZFS", ext4Part);

		SWTBotCommons.checkParentChildRelation(SWTBotCommons.getFeaturePart(serverEditor, "fs.FileSystem"),
				SWTBotCommons.getFeaturePart(serverEditor, "fs.EXT4"), SWTBotCommons.getFeaturePart(serverEditor, "fs.ZFS"));
		bot.menu("Edit").menu("Undo " + StringTable.RENAME_FEATURE).click();
		bot.menu("Edit").menu("Undo " + StringTable.CREATE_SIBLING).click();
	}

	/**
	 * Test feature group changes: <br> Mark the "FileSystem"-Group as Alternative; assert the "fs.FileSystem"-Group also is an alternative.
	 */
	@Test
	public void changeGroupAlternativeTest() {
		fsEditor.show();
		final SWTBotGefEditPart fsPart = SWTBotCommons.getFeaturePart(fsEditor, "FileSystem");
		SWTBotCommons.changeGroupType(fsEditor, fsPart, ChangeFeatureGroupTypeOperation.ALTERNATIVE);

		final SWTBotGefEditPart fsImportPart = SWTBotCommons.getFeaturePart(serverEditor, "fs.FileSystem");
		assertTrue(SWTBotCommons.extractFeature(fsImportPart).getStructure().isAlternative());
		fsEditor.show();
		bot.menu("Edit").menu("Undo " + StringTable.CHANGE_GROUP_TYPE).click();
	}

	/**
	 * Test feature group changes: <br> Mark the "OperatingSystem"-Group as Or; assert the "fs.FileSystem"-Group also is an or.
	 */
	@Test
	public void changeGroupOrTest() {
		osEditor.show();
		final SWTBotGefEditPart osPart = SWTBotCommons.getFeaturePart(osEditor, "OperatingSystem");
		SWTBotCommons.changeGroupType(osEditor, osPart, ChangeFeatureGroupTypeOperation.OR);

		final SWTBotGefEditPart osImportPart = SWTBotCommons.getFeaturePart(serverEditor, "os.OperatingSystem");
		assertTrue(SWTBotCommons.extractFeature(osImportPart).getStructure().isOr());
		bot.menu("Edit").menu("Undo " + StringTable.CHANGE_GROUP_TYPE).click();
	}

	/**
	 * Test mandatory property: <br> Mark the "OperatingSystem"-Group as And; then mark "Windows" as mandatory, then not.
	 */
	@Test
	public void changeMandatoryTest() {
		osEditor.show();
		final SWTBotGefEditPart osGroup = SWTBotCommons.getFeaturePart(osEditor, "OperatingSystem");
		final SWTBotGefEditPart windowsPart = SWTBotCommons.getFeaturePart(osEditor, "Windows");
		final IFeatureStructure windowsImportStructure = SWTBotCommons.extractStructure(SWTBotCommons.getFeaturePart(serverEditor, "os.Windows"));

		SWTBotCommons.changeGroupType(osEditor, osGroup, ChangeFeatureGroupTypeOperation.AND);
		SWTBotCommons.markFeature(osEditor, windowsPart, StringTable.MANDATORY_UPPERCASE, true);
		assertTrue(windowsImportStructure.isMandatory());
		SWTBotCommons.markFeature(osEditor, windowsPart, StringTable.MANDATORY_UPPERCASE, false);
		assertFalse(windowsImportStructure.isMandatory());

		bot.menu("Edit").menu("Undo " + StringTable.MANDATORY_OPERATION).click();
		bot.menu("Edit").menu("Undo " + StringTable.MANDATORY_OPERATION).click();
		bot.menu("Edit").menu("Undo " + StringTable.CHANGE_GROUP_TYPE).click();
	}

	/**
	 * Test abstract property: <br> Mark "FileSystem" as concrete and "OperatingSystem" as abstract; check property propagation in Server, then reset values.
	 */
	@Test
	public void changeAbstractTest() {
		fsEditor.show();
		final SWTBotGefEditPart fsPart = SWTBotCommons.getFeaturePart(fsEditor, "FileSystem");
		SWTBotCommons.markFeature(fsEditor, fsPart, StringTable.ABSTRACT_ACTION, true);
		assertTrue(SWTBotCommons.extractStructure(SWTBotCommons.getFeaturePart(serverEditor, "fs.FileSystem")).isAbstract());

		osEditor.show();
		final SWTBotGefEditPart osPart = SWTBotCommons.getFeaturePart(osEditor, "OperatingSystem");
		SWTBotCommons.markFeature(osEditor, osPart, StringTable.ABSTRACT_ACTION, false);
		assertFalse(SWTBotCommons.extractStructure(SWTBotCommons.getFeaturePart(serverEditor, "os.OperatingSystem")).isAbstract());

		fsEditor.show();
		bot.menu("Edit").menu("Undo " + StringTable.ABSTRACT_OPERATION).click();
		osEditor.show();
		bot.menu("Edit").menu("Undo " + StringTable.ABSTRACT_OPERATION).click();
	}

	/**
	 * Test constraint addition and removal: <br> Add to OperatingSystem the constraint "os.Windows or os.OperatingSystem", then delete it. Assume it exists in
	 * Server as well, but not as an own constraint.
	 */
	@Test
	public void addAndDeleteConstraintTest() {
		osEditor.show();
		final SWTBotGefEditPart newConstraintPart = SWTBotCommons.createConstraint(osEditor, "Windows implies OperatingSystem");
		final SWTBotGefEditPart importConsPart = SWTBotCommons.getConstraintPart(serverEditor, "os.Windows implies os.OperatingSystem");
		final IConstraint importCons = SWTBotCommons.extractConstraint(importConsPart);
		assertFalse(((MultiFeatureModel) importCons.getFeatureModel()).getOwnConstraints().contains(importCons));

		SWTBotCommons.deleteConstraint(osEditor, newConstraintPart);
		assertEquals(-1, importCons.getFeatureModel().getConstraintIndex(importCons));

		bot.menu("Edit").menu("Undo " + StringTable.DELETE).click();
		bot.menu("Edit").menu("Undo " + StringTable.CREATE_CONSTRAINT).click();
	}

	/**
	 * Creates a new feature <code>Compression</code> in <code>FileSystem</code>. Creates a new constraint and modifies it. The modified constraint should now
	 * be visible in the <code>Server</code> editor.
	 */
	@Test
	public void addAndChangeConstraintTest() {
		fsEditor.show();
		final SWTBotGefEditPart fs = SWTBotCommons.getFeaturePart(fsEditor, "FileSystem");
		SWTBotCommons.createFeatureBelow(fsEditor, "Compression", fs);
		final String oldFormula = "Compression implies EXT4";
		SWTBotCommons.createConstraint(fsEditor, oldFormula);
		final String newFormula = "Compression implies EXT4 or NTFS";
		SWTBotCommons.openConstraintDialog(fsEditor, oldFormula, newFormula);

		final SWTBotGefEditPart importConstraintPart = SWTBotCommons.prependModelName(serverEditor, "fs", newFormula);
		final IConstraint importCons = SWTBotCommons.extractConstraint(importConstraintPart);
		assertFalse(((MultiFeatureModel) importCons.getFeatureModel()).getOwnConstraints().contains(importCons));

		bot.menu("Edit").menu("Undo " + StringTable.EDIT_CONSTRAINT).click();
		bot.menu("Edit").menu("Undo " + StringTable.CREATE_CONSTRAINT).click();
		bot.menu("Edit").menu("Undo " + StringTable.RENAME_FEATURE).click();
		bot.menu("Edit").menu("Undo " + StringTable.CREATE_FEATURE_BELOW).click();
	}

	/**
	 * Creates and deletes immediately afterwards the feature <code>ZFS</code> as child of <code>FileSystem</code>. Then, the imported <code>fs.ZFS</code>
	 * feature should not exist in the <code>Server</code> editor as well.
	 */
	@Test
	public void deleteFeatureTest() {
		fsEditor.show();
		final SWTBotGefEditPart zfsPart = SWTBotCommons.createFeatureBelow(fsEditor, "ZFS", SWTBotCommons.getFeaturePart(fsEditor, "FileSystem"));
		final IFeature zfsImportedFeature = SWTBotCommons.extractFeature(SWTBotCommons.getFeaturePart(serverEditor, "fs.ZFS"));
		SWTBotCommons.deleteFeature(fsEditor, zfsPart);
		assertFalse(zfsImportedFeature.getFeatureModel().getFeatures().contains(zfsImportedFeature));

		bot.menu("Edit").menu("Undo " + StringTable.DELETE).click();
		bot.menu("Edit").menu("Undo " + StringTable.RENAME_FEATURE).click();
		bot.menu("Edit").menu("Undo " + StringTable.CREATE_FEATURE_BELOW).click();
	}

	/**
	 * Create the feature <code>GUI</code> below <code>Debian</code> in <code>OperatingSystem</code> and the constraint <code>GUI or Debian</code>. Then delete
	 * <code>GUI</code> with slicing. Assert that the previous constraint and the GUI import do not appear in <code>Server</code>, but every new constraint
	 * does.
	 */
	@Test
	public void deleteFeatureWithSlicingTest() {
		osEditor.show();
		final SWTBotGefEditPart guiPart = SWTBotCommons.createFeatureBelow(osEditor, "GUI", SWTBotCommons.getFeaturePart(osEditor, "Debian"));
		final SWTBotGefEditPart guiConsPart = SWTBotCommons.createConstraint(osEditor, "Debian or GUI");

		final IFeature guiImportFeature = SWTBotCommons.extractFeature(SWTBotCommons.getFeaturePart(serverEditor, "os.GUI"));
		final IConstraint guiImportCons = SWTBotCommons.extractConstraint(SWTBotCommons.getConstraintPart(serverEditor, "os.Debian or os.GUI"));

		SWTBotCommons.checkDeleteWithSlicingOptions(osEditor, guiPart, true, false);
		final IFeatureModel serverModel = guiImportCons.getFeatureModel();
		assertFalse(serverModel.getConstraints().contains(guiImportCons));
		assertFalse(serverModel.getFeatures().contains(guiImportFeature));

		final IConstraint guiCons = SWTBotCommons.extractConstraint(guiConsPart);
		for (final IConstraint cons : SWTBotCommons.extractFeature(SWTBotCommons.getFeaturePart(osEditor, "Debian")).getFeatureModel().getConstraints()) {
			SWTBotCommons.prependModelName(serverEditor, "os", cons.getNode().toString(NodeWriter.textualSymbols));
		}
	}

	/**
	 * Attempts to delete the <code>APFS</code> feature from <code>FileSystem</code>. This should produce a warning instead that this feature appears in an
	 * imported constraint in another model.
	 */
	@Test
	public void deleteFeatureProhibitedTest() {
		fsEditor.show();

		final SWTBotGefEditPart apfsPart = SWTBotCommons.getFeaturePart(fsEditor, "APFS");
		final IFeatureModel modelBeforeExecution = SWTBotCommons.extractFeature(apfsPart).getFeatureModel().clone();
		final IFeatureModel newModel = SWTBotCommons.checkDeleteWithSlicingOptions(fsEditor, apfsPart, false, false);
		assertEquals(modelBeforeExecution, newModel);
	}

	/**
	 * Test drag and drop of features: <br> Move <code>EXT4</code> below <code>NTFS</code>. Assert its new parent is NTFS. Also check that <code>fs.EXT4</code>
	 * now has <code>fs.NTFS</code> as new parent. <br> Now activate manual layout and move <code>EXT4</code> below <code>APFS</code>. Assert that the parent
	 * stays the same.
	 */
	@Test
	public void moveFeatureTest() {
		fsEditor.show();

		final SWTBotGefEditPart ext4Part = SWTBotCommons.getFeaturePart(fsEditor, "EXT4");
		final SWTBotGefEditPart ntfsPart = SWTBotCommons.getFeaturePart(fsEditor, "NTFS");
		SWTBotCommons.moveBelow(fsEditor, ext4Part, ntfsPart, true);

		final IFeature ext4Import = SWTBotCommons.extractFeature(SWTBotCommons.getFeaturePart(serverEditor, "fs.EXT4"));
		final IFeature ntfsImport = SWTBotCommons.extractFeature(SWTBotCommons.getFeaturePart(serverEditor, "fs.NTFS"));
		assertEquals(ntfsImport, ext4Import.getStructure().getParent().getFeature());

		fsEditor.click(1, 1);
		fsEditor.clickContextMenu(StringTable.SET_LAYOUT).clickContextMenu(StringTable.MANUAL_LAYOUT);

		SWTBotCommons.moveBelow(fsEditor, ext4Part, SWTBotCommons.getFeaturePart(fsEditor, "APFS"), false);
		assertEquals(ntfsImport, ext4Import.getStructure().getParent().getFeature());

		bot.menu("Edit").menu("Undo " + StringTable.MOVE_FEATURE).click();
		bot.menu("Edit").menu("Undo " + StringTable.SET_MANUAL_LAYOUT).click();
		bot.menu("Edit").menu("Undo " + StringTable.MOVE_FEATURE).click();
	}

	/**
	 * Tests feature reversal: Reverse the features in <code>OperatingSystem</code>. Assert the child features order is reversed in <code>OperatingSystem</code>
	 * and <code>Server</code>.
	 */
	@Test
	public void reverseFeatureTreeOrderTest() {
		final IFeature osFeature = SWTBotCommons.extractFeature(SWTBotCommons.getFeaturePart(osEditor, "OperatingSystem"));
		final List<IFeature> osChildren = SWTBotCommons.getChildrenFeatures(osFeature);

		final IFeature osImportFeature = SWTBotCommons.extractFeature(SWTBotCommons.getFeaturePart(serverEditor, "os.OperatingSystem"));
		final List<IFeature> osImportChildren = SWTBotCommons.getChildrenFeatures(osImportFeature);

		osEditor.show();
		osEditor.click(1, 1);
		osEditor.clickContextMenu(StringTable.REVERSE_FEATURE_ORDER);

		Collections.reverse(osImportChildren);
		assertEquals(osImportChildren, SWTBotCommons.getChildrenFeatures(osImportFeature));
		Collections.reverse(osChildren);
		assertEquals(osChildren, SWTBotCommons.getChildrenFeatures(osFeature));

		bot.menu("Edit").menu("Undo " + StringTable.REVERSE_LAYOUT_ORDER).click();
	}

	/**
	 * Closes the IDE.
	 */
	@AfterClass
	public static void cleanup() {}
}
