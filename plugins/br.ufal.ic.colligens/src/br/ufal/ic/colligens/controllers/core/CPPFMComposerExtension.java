package br.ufal.ic.colligens.controllers.core;

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
 * @author Francisco Dalton
 * thanks to:
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
public class CPPFMComposerExtension extends FMComposerExtension {

	private static String ORDER_PAGE_MESSAGE = "FeatureIDE projects based on preprocessors such as CPPs do not\n"
			+ "need an order, as the order is given directly at the source code.";

	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}

	@Override
	public boolean hasFeaureOrder() {
		return false;
	}

	@Override
	public boolean performRenaming(String oldName, String newName,
			IProject project) {
		IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		IFolder sourceFolder = featureProject.getSourceFolder();
		System.out.println(sourceFolder.getFullPath().toOSString());
		if (!sourceFolder.exists())
			return true;

		try {
			performRenamings(oldName, newName, sourceFolder);
			sourceFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return true;
	}

	private void performRenamings(String oldName, String newName, IFolder folder)
			throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				performRenamings(oldName, newName, (IFolder) res);
			} else if (res instanceof IFile) {
				IFile file = (IFile) res;
				performRenamings(oldName, newName, file);
			}

		}
	}

	private void performRenamings(String oldName, String newName, IFile iFile) {
		Scanner scanner = null;
		FileWriter fw = null;
		try {
			File file = iFile.getRawLocation().toFile();

			StringBuilder fileText = new StringBuilder();
			scanner = new Scanner(file, "UTF-8");
			while (scanner.hasNext()) {
				fileText.append(scanner.nextLine());
				fileText.append(System.getProperty("line.separator"));
			}

			String newText = replaceFeatureInText(fileText.toString(), oldName,
					newName);

			if (fileText.toString().equals(newText)) {
				return;
			}

			fw = new FileWriter(file);
			fw.write(newText);

		} catch (FileNotFoundException e) {
			Colligens.getDefault().logError(e);
		} catch (IOException e) {
			Colligens.getDefault().logError(e);
		} finally {
			if (scanner != null)
				scanner.close();
			if (fw != null)
				try {
					fw.close();
				} catch (IOException e) {
					Colligens.getDefault().logError(e);
				}
		}
	}

	private String replaceFeatureInText(String text, String oldName,
			String newName) {
		Pattern pattern = Pattern.compile(String.format(CPPModelBuilder.REGEX,
				oldName));
		Matcher matcher = pattern.matcher(text);

		while (matcher.find()) {
			String newText = matcher.group(1) + newName + matcher.group(3);
			text = text.replace(matcher.group(0), newText);
			matcher.reset(text);
		}

		return text;
	}
}