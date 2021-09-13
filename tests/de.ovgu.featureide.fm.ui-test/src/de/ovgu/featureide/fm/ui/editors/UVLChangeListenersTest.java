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

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditPart;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;

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
	}

	/**
	 * Test name propagation: <br> Change the name of "Windows" in OperatingSystem to "Windows 10"; assert that the name changes in OperatingSystem and Server.
	 */
	@Test
	public void namePropagationTest() {
		final SWTBotGefEditPart windowsPart = SWTBotCommons.getFeaturePart(osEditor, "Windows");
		SWTBotCommons.renameFeature(osEditor, windowsPart, "Windows_10");
		SWTBotCommons.getFeaturePart(serverEditor, "os.Windows_10");
	}

	/**
	 * Test feature creation above: <br> Select features "Debian" and "macOS"; then create a new feature called "Unix" above.
	 */
	@Test
	public void featureAddAboveTest() {}

	@Test
	public void featureAddBelowTest() {}

	@Test
	public void featureAddSiblingTest() {}

	@Test
	public void changeGroupAlternativeTest() {}

	@Test
	public void changeGroupOrTest() {}

	@Test
	public void changeMandatoryTest() {}

	@Test
	public void changeAlternativeTest() {}

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
	 * Presses CTRL+Z to undo the previous command. Asserts that the underlying models of all editors are all as they were previously.
	 */
	@After
	public void undoChange() {

	}

	/**
	 * Closes the IDE.
	 */
	@AfterClass
	public static void cleanup() {
		bot.menu("File").menu("Exit").click();
	}
}
