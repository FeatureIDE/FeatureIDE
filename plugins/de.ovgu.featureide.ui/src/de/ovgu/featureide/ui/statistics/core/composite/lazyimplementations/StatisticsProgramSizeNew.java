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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURES;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * TreeNode who stores the number of classes, roles, fields and methods of a given {@link FSTModel}.<br> This node should only be used for a feature oriented
 * project.
 *
 * @author Schleicher Miro
 */
public class StatisticsProgramSizeNew extends LazyParent {

	private final static String[] ignoredExtensions =
		{ "jpg", "jpeg", "raw", "hdr", "tiff", "bmp", "jpe", "dib", "gif", "pdf", "png", "zip", "wav", "mp3", "avi", "flv", "midi" };

	private final HashMap<String, Integer> featureExtensionLOCList = new HashMap<String, Integer>();
	private final FSTModel fstModel;

	private int numberOfLines = 0;

	public StatisticsProgramSizeNew(String description, FSTModel fstModel) {
		super(description);
		this.fstModel = fstModel;
	}

	@Override
	protected void initChildren() {

		int numberOfClasses = 0;
		int numberOfRoles = 0;
		int numberOfFields = 0;
		int numberOfUniFields = 0;
		int numberOfMethods = 0;
		int numberOfUniMethods = 0;

		for (final FSTClass fstClass : fstModel.getClasses()) {
			final List<List<FSTClassFragment>> allFrag = fstClass.getAllFSTFragments();
			final HashSet<FSTMethod> methHelper = new HashSet<FSTMethod>();
			final HashSet<FSTField> fieldHelper = new HashSet<FSTField>();

			for (final List<FSTClassFragment> linkedList : allFrag) {
				numberOfRoles += linkedList.size();

				for (final FSTClassFragment fstClassFragment : linkedList) {
					methHelper.addAll(fstClassFragment.getMethods());
					fieldHelper.addAll(fstClassFragment.getFields());

					numberOfMethods += fstClassFragment.getMethods().size();
					numberOfFields += fstClassFragment.getFields().size();
				}
			}

			numberOfUniFields += fieldHelper.size();
			numberOfUniMethods += methHelper.size();
			numberOfClasses += allFrag.size();
		}

		if (fstModel.getFeatureProject().getComposer().hasFeatureFolder()) {
			try {
				checkLOC();
			} catch (final CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		}

		addChild(new SumImplementationArtifactsParent(NUMBER_CLASS + SEPARATOR + numberOfClasses + " | " + NUMBER_ROLE + SEPARATOR + numberOfRoles, fstModel,
				SumImplementationArtifactsParent.NUMBER_OF_CLASSES));
		addChild(new SumImplementationArtifactsParent(NUMBER_FIELD_U + SEPARATOR + numberOfUniFields + " | " + NUMBER_FIELD + SEPARATOR + numberOfFields,
				fstModel, SumImplementationArtifactsParent.NUMBER_OF_FIELDS));
		addChild(new SumImplementationArtifactsParent(NUMBER_METHOD_U + SEPARATOR + numberOfUniMethods + " | " + NUMBER_METHOD + SEPARATOR + numberOfMethods,
				fstModel, SumImplementationArtifactsParent.NUMBER_OF_METHODS));
		addChild(new LOCNode(NUMBER_OF_CODELINES + SEPARATOR + numberOfLines, featureExtensionLOCList));
	}

	private static boolean isIgnoredExtension(String fileExtension) {
		for (final String extension : ignoredExtensions) {
			if (extension.equals(fileExtension)) {
				return true;
			}
		}
		return false;
	}

	public void checkLOC() throws CoreException {
		fstModel.getFeatureProject().getSourceFolder().accept(new IResourceVisitor() {

			@Override
			public boolean visit(IResource resource) throws CoreException {
				int numberOfLinesInThisFile = 0;
				if (resource instanceof IFolder) {
					return true;
				} else if (resource instanceof IFile) {
					final IFile file = (IFile) resource;
					String oneLineComment = "", moreLineStart = "", moreLineEnd = "";

					if (!isIgnoredExtension(file.getFileExtension())) {
						switch (file.getFileExtension()) {
						// TODO complete for all extensions
						case "java":
						case "c":
						case "h":
						case "jj":
						case "jak":
							oneLineComment = "//";
							moreLineStart = "/*";
							moreLineEnd = "*/";
							break;
						case "cs":
							oneLineComment = "///";
							moreLineStart = "/*";
							moreLineEnd = "*/";
							break;
						// TODO Haskell comments
						// case "hs":
						// oneLineComment = "--";
						// moreLineStart = "{-";
						// moreLineEnd = "-}";
						// break;
						case "als":
						case "xmi":
							break;
						default:
							oneLineComment = "#|#|#";
							moreLineStart = "#|#|#";
							moreLineEnd = "#|#|#";
							break;
						}

						try {
							numberOfLinesInThisFile = countLOC(file, oneLineComment, moreLineStart, moreLineEnd/* , nested, nestedCounter */);

						} catch (final FileNotFoundException e) {
							e.printStackTrace();
						} catch (final IOException e) {
							e.printStackTrace();
						}

						final String feat = (file.getFullPath().toString().substring(file.getFullPath().toString().indexOf(FEATURES) + 9,
								file.getFullPath().toString().length() - 1)).split("/")[0];

						if (!featureExtensionLOCList.containsKey(file.getFileExtension() + "#" + feat)) {
							featureExtensionLOCList.put(file.getFileExtension() + "#" + feat, numberOfLinesInThisFile);
						} else {
							featureExtensionLOCList.put(file.getFileExtension() + "#" + feat,
									featureExtensionLOCList.get(file.getFileExtension() + "#" + feat) + numberOfLinesInThisFile);
						}
					}
				}
				numberOfLines += numberOfLinesInThisFile;

				return false;
			}

		});
	}

	public static int countLOC(final IFile file, String oneLineComment, String moreLineStart, String moreLineEnd) throws FileNotFoundException, IOException {
		final FileReader fr = new FileReader(file.getLocation().toString());
		final BufferedReader br = new BufferedReader(fr);
		return countLineNumber(oneLineComment, moreLineStart, moreLineEnd, br);
	}

	public static int countLineNumber(String oneLineComment, String moreLineStart, String moreLineEnd, BufferedReader br) throws IOException {
		int numberOfLinesInThisFile = 0;
		String s;
		boolean isInComment = false;
		while ((s = br.readLine()) != null) {
			s = s.trim();
			if (!s.equals("") && !s.startsWith(oneLineComment) && !isInComment) {
				if (s.startsWith(moreLineStart)) {
					isInComment = true;
				} else {
					numberOfLinesInThisFile++;
				}
			}

			if (s.contains(moreLineEnd)) {

				isInComment = false;
				if (!s.endsWith(moreLineEnd)) {
					numberOfLinesInThisFile++;
				}
			}

			if (s.contains(moreLineStart) && !s.startsWith("/*")) {
				isInComment = true;
			}
		}
		br.close();
		return numberOfLinesInThisFile;
	}

}
