package br.ufal.ic.colligens.controllers.core;

import static de.ovgu.featureide.fm.core.localization.StringTable.NEED_AN_ORDER_COMMA__AS_THE_ORDER_IS_GIVEN_DIRECTLY_AT_THE_SOURCE_CODE_;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import br.ufal.ic.colligens.activator.Colligens;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FMComposerExtension;
import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * CPP specific feature model extensions.
 *
 * @author Francisco Dalton thanks to:
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
public class CPPFMComposerExtension extends FMComposerExtension {

	private static String ORDER_PAGE_MESSAGE =
		"FeatureIDE projects based on preprocessors such as CPPs do not\n" + NEED_AN_ORDER_COMMA__AS_THE_ORDER_IS_GIVEN_DIRECTLY_AT_THE_SOURCE_CODE_;

	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}

	@Override
	public boolean hasFeatureOrder() {
		return false;
	}

	@Override
	public boolean performRenaming(String oldName, String newName, IProject project) {
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		final IFolder sourceFolder = featureProject.getSourceFolder();
		System.out.println(sourceFolder.getFullPath().toOSString());
		if (!sourceFolder.exists()) {
			return true;
		}

		try {
			performRenamings(oldName, newName, sourceFolder);
			sourceFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return true;
	}

	private void performRenamings(String oldName, String newName, IFolder folder) throws CoreException {
		for (final IResource res : folder.members()) {
			if (res instanceof IFolder) {
				performRenamings(oldName, newName, (IFolder) res);
			} else if (res instanceof IFile) {
				final IFile file = (IFile) res;
				performRenamings(oldName, newName, file);
			}

		}
	}

	private void performRenamings(String oldName, String newName, IFile iFile) {
		Scanner scanner = null;
		FileWriter fw = null;
		try {
			final File file = iFile.getRawLocation().toFile();

			final StringBuilder fileText = new StringBuilder();
			scanner = new Scanner(file, "UTF-8");
			while (scanner.hasNext()) {
				fileText.append(scanner.nextLine());
				fileText.append(System.getProperty("line.separator"));
			}

			final String newText = replaceFeatureInText(fileText.toString(), oldName, newName);

			if (fileText.toString().equals(newText)) {
				return;
			}

			fw = new FileWriter(file);
			fw.write(newText);

		} catch (final FileNotFoundException e) {
			Colligens.getDefault().logError(e);
		} catch (final IOException e) {
			Colligens.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
			if (fw != null) {
				try {
					fw.close();
				} catch (final IOException e) {
					Colligens.getDefault().logError(e);
				}
			}
		}
	}

	private String replaceFeatureInText(String text, String oldName, String newName) {
		final Pattern pattern = Pattern.compile(String.format(CPPModelBuilder.REGEX, oldName));
		final Matcher matcher = pattern.matcher(text);

		while (matcher.find()) {
			final String newText = matcher.group(1) + newName + matcher.group(3);
			text = text.replace(matcher.group(0), newText);
			matcher.reset(text);
		}

		return text;
	}
}
