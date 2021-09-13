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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditPart;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;

import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ChangeFeatureGroupTypeOperation;

/**
 * Tests that the UVL model changes are propagated correctly from submodels. Uses the Universal-Variability-Language-Multi example. Provides (GUI) tests for
 * Issue #1134.
 *
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
	 * submodels/FileSystem.uvl, OperatingSystem.uvl, and Server.uvl.
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
		final SWTBotGefEditPart fsPart = SWTBotCommons.getFeaturePart(fsEditor, "FileSystem");
		SWTBotCommons.changeGroupType(fsEditor, fsPart, ChangeFeatureGroupTypeOperation.ALTERNATIVE);

		final SWTBotGefEditPart fsImportPart = SWTBotCommons.getFeaturePart(serverEditor, "fs.FileSystem");
		assertTrue(SWTBotCommons.extractFeature(fsImportPart).getStructure().isAlternative());
		bot.menu("Edit").menu("Undo " + StringTable.CHANGE_GROUP_TYPE).click();
	}

	/**
	 * Test feature group changes: <br> Mark the "OperatingSystem"-Group as Or; assert the "fs.FileSystem"-Group also is an or.
	 */
	@Test
	public void changeGroupOrTest() {
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
		final SWTBotGefEditPart osGroup = SWTBotCommons.getFeaturePart(osEditor, "OperatingSystem");
		final SWTBotGefEditPart windowsPart = SWTBotCommons.getFeaturePart(osEditor, "Windows");
		final IFeatureStructure windowsImportStructure = SWTBotCommons.extractStructure(SWTBotCommons.getFeaturePart(serverEditor, "os.Windows"));

		SWTBotCommons.changeGroupType(osEditor, osGroup, ChangeFeatureGroupTypeOperation.AND);
		SWTBotCommons.markFeature(osEditor, windowsPart, StringTable.MANDATORY_UPPERCASE, true);
		assertTrue(windowsImportStructure.isMandatory());
		SWTBotCommons.markFeature(osEditor, windowsPart, StringTable.MANDATORY_UPPERCASE, false);
		assertFalse(windowsImportStructure.isMandatory());

		osEditor.show();
		bot.menu("Edit").menu("Undo " + StringTable.MANDATORY_OPERATION).click();
		bot.menu("Edit").menu("Undo " + StringTable.MANDATORY_OPERATION).click();
		bot.menu("Edit").menu("Undo " + StringTable.CHANGE_GROUP_TYPE).click();
	}

	/**
	 * Test abstract property: <br> Mark "FileSystem" as concrete and "OperatingSystem" as abstract; check property propagation in Server, then reset values.
	 */
	@Test
	public void changeAbstractTest() {
		final SWTBotGefEditPart fsPart = SWTBotCommons.getFeaturePart(fsEditor, "FileSystem");
		SWTBotCommons.markFeature(fsEditor, fsPart, StringTable.ABSTRACT_ACTION, true);
		assertTrue(SWTBotCommons.extractStructure(SWTBotCommons.getFeaturePart(serverEditor, "fs.FileSystem")).isAbstract());

		final SWTBotGefEditPart osPart = SWTBotCommons.getFeaturePart(osEditor, "OperatingSystem");
		SWTBotCommons.markFeature(osEditor, osPart, StringTable.ABSTRACT_ACTION, false);
		assertFalse(SWTBotCommons.extractStructure(SWTBotCommons.getFeaturePart(serverEditor, "os.OperatingSystem")).isAbstract());

		fsEditor.show();
		bot.menu("Edit").menu("Undo " + StringTable.ABSTRACT_OPERATION).click();
		osEditor.show();
		bot.menu("Edit").menu("Undo " + StringTable.ABSTRACT_OPERATION).click();
	}

	@Test
	public void addAndDeleteConstraintTest() {}

	@Test
	public void addAndChangeConstraintTest() {}

	@Test
	public void deleteFeatureTest() {}

	@Test
	public void deleteFeatureWithSlicingTest() {}

	@Test
	public void deleteFeatureProhibitedTest() {}

	@Test
	public void moveFeatureTest() {}

	@Test
	public void reverseFeatureTreeOrderTest() {}

	@Test
	public void propagateInTextEditorTest() {}

	/**
	 * Closes the IDE.
	 */
	@AfterClass
	public static void cleanup() {
		// bot.menu("File").menu("Exit").click();
	}
}
