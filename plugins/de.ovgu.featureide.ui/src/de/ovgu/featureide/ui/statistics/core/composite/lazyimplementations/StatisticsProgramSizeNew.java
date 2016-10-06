/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistrisFeatureOrPreprocessorProjectt and/or modify
 * it under the terms of theisFeatureOrPreprocessorProjectsser GeneisFeatureOrPreprocessorProjectlic License as published by
 * isFeatureOrPreprocessorProjecte Software Foundation, either version 3 of the License, or
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

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.TreeSet;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass.Mechanism;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.datatypes.FileFeatureLOCMapper;

/**
 * TreeNode who stores the number of classes, roles, fields and methods of a
 * given {@link FSTModel}.<br>
 * This node should only be used for a feature oriented project.
 * 
 * @author Schleicher Miro
 * @author Maximilian Homann
 * @author Philipp Kuhn
 */
public class StatisticsProgramSizeNew extends LazyParent {

	private final static String[] ignoredExtensions = { "jpg", "jpeg", "raw", "hdr", "tiff", "bmp", "jpe", "dib", "gif", "pdf", "png", "zip", "wav", "mp3",
			"avi", "flv", "midi" };

	private final FSTModel fstModel;
	private final FileFeatureLOCMapper fileFeatLOCMapper;
	private int numberOfLines = 0;
	private boolean isPPProject = false;
	private boolean isFeatureOrPreprocessorProject = false;
	private IFeatureProject project;
	
	public StatisticsProgramSizeNew(String description, FSTModel fstModel, IFeatureProject project) {
		super(description);
		this.fstModel = fstModel;
		this.project = project;
		this.fileFeatLOCMapper = new FileFeatureLOCMapper(project.getSourceFolder());
		this.isFeatureOrPreprocessorProject = true;
	}
	/**
	 * Constructor for AspectOrientated projects
	 * @param description
	 * @param project
	 */
	
	public StatisticsProgramSizeNew(String description, IFeatureProject project) {
		super(description);
		this.fstModel = null;
		this.project = project;
		this.isFeatureOrPreprocessorProject = false;
		this.fileFeatLOCMapper = new FileFeatureLOCMapper(project.getSourceFolder());
	}

	@Override
	protected void initChildren() {

		int numberOfClasses = 0;
		int numberOfRoles = 0;
		int numberOfFields = 0;
		int numberOfUniFields = 0;
		int numberOfMethods = 0;
		int numberOfUniMethods = 0;

		if(isFeatureOrPreprocessorProject) {
			for (FSTClass fstClass : fstModel.getClasses()) {
				final List<List<FSTClassFragment>> allFrag = fstClass.getAllFSTFragments();
				final HashSet<FSTMethod> methHelper = new HashSet<FSTMethod>();
				final HashSet<FSTField> fieldHelper = new HashSet<FSTField>();
	
				for (List<FSTClassFragment> linkedList : allFrag) {
					numberOfRoles += linkedList.size();
	
					for (FSTClassFragment fstClassFragment : linkedList) {
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
		}
		
		try {
			checkLOC();
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}

		if (project.getComposer().getGenerationMechanism() == Mechanism.FEATURE_ORIENTED_PROGRAMMING) {
			addChild(new SumImplementationArtifactsParent(NUMBER_CLASS + SEPARATOR + numberOfClasses + " | " + NUMBER_ROLE + SEPARATOR + numberOfRoles, fstModel,
					SumImplementationArtifactsParent.NUMBER_OF_CLASSES));
			addChild(new SumImplementationArtifactsParent(NUMBER_FIELD_U + SEPARATOR + numberOfUniFields + " | " + NUMBER_FIELD + SEPARATOR + numberOfFields,
					fstModel, SumImplementationArtifactsParent.NUMBER_OF_FIELDS));
			addChild(new SumImplementationArtifactsParent(NUMBER_METHOD_U + SEPARATOR + numberOfUniMethods + " | " + NUMBER_METHOD + SEPARATOR + numberOfMethods,
					fstModel, SumImplementationArtifactsParent.NUMBER_OF_METHODS));
		}
		boolean isPreprocessor = false;
		if (project.getComposer().getGenerationMechanism() == Mechanism.PREPROCESSOR) {
			isPreprocessor = true;
			isFeatureOrPreprocessorProject = true;
		}
		addChild(new LOCNode(NUMBER_OF_CODELINES + SEPARATOR + numberOfLines, fileFeatLOCMapper, isPreprocessor));
	}

	private static boolean isIgnoredExtension(String fileExtension) {
		for (String extension : ignoredExtensions) {
			if (extension.equals(fileExtension)) {
				return true;
			}
		}
		return false;
	}

	public void checkLOC() throws CoreException {
		project.getSourceFolder().accept(new IResourceVisitor() {

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
						//TODO complete for all extensions 
						case "java":
						case "c":
						case "h":
						case "jj":
						case "aj":
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
						//	TODO Haskell comments
						//	case "hs":
						//	oneLineComment = "--";
						//	moreLineStart = "{-";
						//	moreLineEnd = "-}";
						//	break;
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
							numberOfLinesInThisFile = countLOC(file, oneLineComment, moreLineStart, moreLineEnd);
						} catch (FileNotFoundException e) {
							e.printStackTrace();
						} catch (IOException e) {
							e.printStackTrace();
						}
						
						Mechanism mecha = project.getComposer().getGenerationMechanism();
						if (mecha == Mechanism.PREPROCESSOR) {
							isPPProject = true;
							numberOfLinesInThisFile += getDirectiveCommandLOC(file);
						}
						//File with loc > Mapper
						fileFeatLOCMapper.addEntry(file, numberOfLinesInThisFile);
						
					}
				}
				numberOfLines += numberOfLinesInThisFile;

				return false;
			}

		});
		if(isFeatureOrPreprocessorProject) {
			fillMapper();
		}
	}
	
	/**
	 * Fills the map inside the FileFeatureLOCMapper with features and lines of code. 
	 */
	private void fillMapper() {
		for (FSTClass fstClass: fstModel.getClasses()) {
			for (FSTRole role: fstClass.getRoles()) {
				FSTFeature currentFeat = role.getFeature();
				IFile file = role.getFile();
				if (isPPProject) {
					
					int loc = countLOCOfDirectives(role.getDirectives());
					fileFeatLOCMapper.addSingleLOCMapEntry(file, currentFeat, loc);
				} else {
					int loc = fileFeatLOCMapper.getLOCByFile(file);
					fileFeatLOCMapper.addSingleLOCMapEntry(file, currentFeat, loc);
				}
				
			}
		}
	}
	
	/**
	 * Counts the lines of code of all directives and adds them to the File Feature LOC Mapper.
	 * @param directives in this file
	 * @return the LOC in all directives
	 */
	private int countLOCOfDirectives(TreeSet<FSTDirective> directives) {
		Iterator<FSTDirective> iterator = directives.iterator();
		int locForDirectives = 0;
		while (iterator.hasNext()) {
			FSTDirective directive = iterator.next();
			int subDirectiveLOC = 0;
			countDirectiveChildrenCommandLOC(directive, subDirectiveLOC);
			locForDirectives += directive.getEndLine() - directive.getStartLine() -1; //From start to end without end command
			locForDirectives -= subDirectiveLOC;
		}
		return locForDirectives;
	}
	
	/**
	 * Recursively counts all command lines of code of a directive and its children
	 * @param directive to count the command code
	 * @param loc recursive variable
	 * @return
	 */
	private int countDirectiveChildrenCommandLOC(FSTDirective directive, int loc) {
		if (directive.hasChildren()) {
			for (FSTDirective child: directive.getChildren()) {
				loc += countDirectiveChildrenCommandLOC(child, loc);
				return loc;
			}
		} else {
			return 2;
		}
		return 0;
	}
	
	/**
	 * Counts the lines of code in file.
	 * 
	 * @param file
	 * @param oneLineComment
	 * @param moreLineStart
	 * @param moreLineEnd
	 * @return the lines of code in file
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
	public int countLOC(final IFile file, String oneLineComment, String moreLineStart, String moreLineEnd) throws FileNotFoundException, IOException {
		FileReader fr = new FileReader(file.getLocation().toString());
		BufferedReader br = new BufferedReader(fr);
		int numberOfLinesInThisFile = 0;
		String line;
		boolean isInComment = false;
		while ((line = br.readLine()) != null) {
			line = line.trim();
			if (!line.equals("") && !line.startsWith(oneLineComment) && !isInComment) {
				if (line.startsWith(moreLineStart)) {
					isInComment = true;
				} else {
					numberOfLinesInThisFile++;
				}
			}

			if (line.contains(moreLineEnd)) {
				isInComment = false;
				if (!line.endsWith(moreLineEnd))
					numberOfLinesInThisFile++;
			}

			if (line.contains(moreLineStart) && !line.startsWith("/*"))
				isInComment = true;
		}
		br.close();
		return numberOfLinesInThisFile;
	}
	
	/**
	 * Counts the lines of code of all directive commands.
	 * @param file
	 * @return
	 */
	private int getDirectiveCommandLOC(IFile file) {
		int loc = 0;
		for (FSTClass fstClass: fstModel.getClasses()) {
			for (FSTRole role: fstClass.getRoles()) {
				if (role.getFile().equals(file)) {
					for (FSTDirective directive: role.getDirectives()) {
						if (!directive.hasChildren() && directive.getParent() == null) {
							loc += 2;
						} else if (directive.hasChildren() && directive.getParent() == null) {
							countDirectiveChildrenCommandLOC(directive, loc);
						}
					}
				}
			}
		}
		return loc;
	}
}
