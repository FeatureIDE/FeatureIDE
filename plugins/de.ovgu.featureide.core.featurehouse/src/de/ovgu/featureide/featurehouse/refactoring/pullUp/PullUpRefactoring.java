/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.resource.DeleteResourceChange;
import org.eclipse.ltk.core.refactoring.resource.MoveResourceChange;
import org.eclipse.text.edits.DeleteEdit;
import org.eclipse.text.edits.InsertEdit;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.eclipse.text.edits.TextEdit;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;
import org.eclipse.ui.texteditor.IDocumentProvider;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.SignaturePosition;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class PullUpRefactoring extends Refactoring {

	private final IFeatureProject featureProject;
	private final AbstractClassSignature selectedElement;
	private final String file;
	private final IFeature sourceFeature;
	private final Map<AbstractSignature, List<ClonedFeatures>> clonedSignatures;
	private IFeature destinationFeature;
	private Set<ExtendedPullUpSignature> pullUpSignatures;
	private Set<ExtendedPullUpSignature> deletableSignatures;
	private List<Change> changes;

	private static final String EXIST_ELEMENT_IN_FEATURE = "A {0} ''{1}'' with this name already exists in feature ''{2}''.";

	@Override
	public String getName() {
		return "Pull Up to Parent-Feature";
	}

	public PullUpRefactoring(AbstractClassSignature selection, IFeatureProject featureProject, String file) {
		this.selectedElement = selection;
		this.featureProject = featureProject;
		this.file = file;
		this.sourceFeature = determineSourceFeature();
		this.clonedSignatures = (new CloneSignatureMatcher(featureProject, selectedElement, file)).computeClonedSignatures();
		;
	}

	private IFeature determineSourceFeature() {
		final AFeatureData featureData = getFeatureDataForFile(selectedElement, file);
		if (featureData == null) return null;

		final ProjectSignatures projectSignatures = featureProject.getProjectSignatures();
		final String featureName = projectSignatures.getFeatureName(featureData.getID());
		return projectSignatures.getFeatureModel().getFeature(featureName);
	}

	protected AFeatureData getFeatureDataForFile(final AbstractSignature signature, final String file) {
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getAbsoluteFilePath().equals(file)) return featureData;
		}
		return null;
	}

	protected AFeatureData getFeatureDataForId(final AbstractSignature signature, final int featureId) {
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getID() == featureId) return featureData;
		}
		return null;
	}

	public IFeature getSourceFeature() {
		return sourceFeature;
	}

	public void setDestinationFeature(IFeature destinationFeature) {
		this.destinationFeature = destinationFeature;
	}

	public IFeature getDestinationFeature() {
		return destinationFeature;
	}

	public void setPullUpSignatures(Set<ExtendedPullUpSignature> pullUpSignatures) {
		this.pullUpSignatures = pullUpSignatures;
	}

	public Set<ExtendedPullUpSignature> getPullUpSignatures() {
		return pullUpSignatures;
	}

	public ProjectSignatures getProjectSignatures() {
		return featureProject.getProjectSignatures();
	}

	public String getFile() {
		return file;
	}

	public IFeatureProject getFeatureProject() {
		return featureProject;
	}

	public AbstractClassSignature getSelectedElement() {
		return selectedElement;
	}

	public Set<ExtendedPullUpSignature> getDeletableSignatures() {
		return deletableSignatures;
	}

	public void setDeletableSignatures(Set<ExtendedPullUpSignature> deletableSignatures) {
		this.deletableSignatures = deletableSignatures;
	}

	public Map<AbstractSignature, List<ClonedFeatures>> getClonedSignatures() {
		return clonedSignatures;
	}

	public Set<AbstractSignature> getPullableElements() {
		final Set<AbstractSignature> result = new HashSet<>();
		addPullableSignature(result, selectedElement);
		addPullableSignatures(result, selectedElement.getMethods());
		addPullableSignatures(result, selectedElement.getFields());
		return result;
	}

	private void addPullableSignatures(final Set<AbstractSignature> result, final Set<? extends AbstractSignature> signatures) {
		for (AbstractSignature abstractSignature : signatures) {
			addPullableSignature(result, abstractSignature);
		}
	}

	private void addPullableSignature(final Set<AbstractSignature> result, AbstractSignature abstractSignature) {
		for (AFeatureData featureData : abstractSignature.getFeatureData()) {
			if (featureData.getAbsoluteFilePath().equals(file)) {
				result.add(abstractSignature);
				break;
			}
		}
	}

	public List<IFeature> getFeatureCandidates() {

		final List<IFeature> features = new ArrayList<>();

		if (sourceFeature == null) return features;

		IFeature parentFeature = sourceFeature.getParent();

		while (parentFeature != null) {
			if (parentFeature.isConcrete()) features.add(0, parentFeature);
			parentFeature = parentFeature.getParent();
		}
		return features;
	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		return new RefactoringStatus();
	}

	@Override
	public RefactoringStatus checkFinalConditions(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		final RefactoringStatus refactoringStatus = new RefactoringStatus();

		try {
			pm.beginTask("Checking preconditions...", 2);

			changes = new ArrayList<Change>();

//			refactoringStatus.merge(createNewDestinationFileIfNotExist());
//			if (refactoringStatus.hasError()) return refactoringStatus;

			refactoringStatus.merge(checkIfPullUpSignaturesExistInFeature());
			if (refactoringStatus.hasError()) return refactoringStatus;

			refactoringStatus.merge(createInsertChanges());
			refactoringStatus.merge(createDeleteChanges());

		} finally {
			pm.done();
		}
		return refactoringStatus;
	}

	private RefactoringStatus checkIfPullUpSignaturesExistInFeature() {

		final RefactoringStatus refactoringStatus = new RefactoringStatus();

		final Set<AbstractSignature> matchedSignatures =
			RefactoringUtil.getIncludedMatchingSignaturesForFile(selectedElement, getDestinationFile().getRawLocation().toOSString());

		for (ExtendedPullUpSignature extendedPullUpSignature : pullUpSignatures) {

			final AbstractSignature signature = extendedPullUpSignature.getSignature();
			if (existSignature(signature, matchedSignatures)) {
				String type;
				if (signature instanceof AbstractMethodSignature) type = "method";
				else if (signature instanceof AbstractFieldSignature) type = "field";
				else type = "class";

				String msg = Messages.format(EXIST_ELEMENT_IN_FEATURE, new String[] { type, signature.getName(), destinationFeature.getName() });
				refactoringStatus.addError(msg);
			}
		}

		return refactoringStatus;
	}

	private boolean existSignature(final AbstractSignature pullUpSignature, final Set<AbstractSignature> matchedSignatures) {

		for (AbstractSignature abstractSignature : matchedSignatures) {
			if (!abstractSignature.getClass().equals(pullUpSignature.getClass())) continue;

			if ((abstractSignature instanceof FujiMethodSignature)
				&& existSignature((FujiMethodSignature) abstractSignature, (FujiMethodSignature) pullUpSignature)) return true;

			if (((abstractSignature instanceof FujiFieldSignature) || (abstractSignature instanceof FujiClassSignature))
				&& existSignature(abstractSignature, pullUpSignature)) return true;
		}
		return false;
	}

	private boolean existSignature(final AbstractSignature sig1, final AbstractSignature sig2) {
		if (sig1.equals(sig2)) return isCodeClone(sig2);
		else return (RefactoringUtil.hasSameName(sig1, sig2) && !sig1.equals(sig2));
	}

	private boolean existSignature(final FujiMethodSignature method1, final FujiMethodSignature method2) {
		if (method1.equals(method2)) return isCodeClone(method1);
		else return RefactoringUtil.hasSameName(method1, method2) && RefactoringUtil.hasSameParameters(method1, method2)
			&& RefactoringUtil.hasSameReturnType(method1, method2);
	}

	private boolean isCodeClone(final AbstractSignature signature) {

		if (!clonedSignatures.containsKey(signature)) return false;
		for (ClonedFeatures clonedFeatures : clonedSignatures.get(signature)) {
			if (!clonedFeatures.getFeatures().contains(destinationFeature)) return true;
		}

		return false;
	}

	@Override
	public Change createChange(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		try {
			pm.beginTask("Creating change...", 1);

			return new CompositeChange(getName(), changes.toArray(new Change[changes.size()]));
		} finally {
			pm.done();
		}
	}

	private RefactoringStatus createInsertChanges() {

		RefactoringStatus status = new RefactoringStatus();
		MultiTextEdit multiEdit = new MultiTextEdit();

		if (pullUpSignatures.size() == 0) return status;

		IFile pullUpFile = RefactoringUtil.getFile(file);

		IFile destinationFile = createNewDestinationFileIfNotExist();

		IDocumentProvider pullUpProvider = new TextFileDocumentProvider();
		IDocumentProvider destinationProvider = new TextFileDocumentProvider();
		try {
			pullUpProvider.connect(pullUpFile);
			destinationProvider.connect(destinationFile);
			final IDocument pullUpDoc = pullUpProvider.getDocument(pullUpFile);
			final IDocument destinationDoc = destinationProvider.getDocument(destinationFile);

			int destinationFeatureId = featureProject.getProjectSignatures().getFeatureID(destinationFeature.getName());

			for (ExtendedPullUpSignature extendedSignature : pullUpSignatures) {

				final AbstractSignature signature = extendedSignature.getSignature();

				AFeatureData featureData = getFeatureDataForId(signature, destinationFeatureId);
				if (featureData != null) continue;

				featureData = getFeatureDataForFile(signature, file);
				if (featureData == null) continue;

				AbstractSignature parent;
				if (signature instanceof FujiClassSignature) {
					MoveResourceChange moveChange = new MoveResourceChange(pullUpFile, destinationFile.getParent());
					changes.add(moveChange);
				} else {
					parent = signature.getParent();
					final AFeatureData destinationFeatureData = getFeatureDataForFile(parent, destinationFile.getRawLocation().toOSString());

					SignaturePosition position = featureData.getSigPosition();

					int startOffset = pullUpDoc.getLineOffset(position.getStartRow() - 1);
					int endOffset = pullUpDoc.getLineOffset(position.getEndRow() - 1);
					String content = "";
					if (signature instanceof FujiFieldSignature) {
//						content += "\t";
//						for (String modifier : signature.getModifiers()) {
//							content += modifier + " ";
//						}
//						
//						((FujiFieldSignature)signature).getFullModifiersAndReturnTypes();

//						content += signature.getType() + " " + signature.getName() +";\n";

						content += ((FujiFieldSignature) signature).getFullFieldDeclaration() + "\n";
					} else {
						endOffset += position.getEndColumn();
						content = pullUpDoc.get(startOffset, endOffset - startOffset) + "\n";
					}

					int line = destinationDoc.getNumberOfLines() - 1;
					if (destinationFeatureData != null) line = destinationFeatureData.getSigPosition().getEndRow() - 1;

					multiEdit.addChild(new InsertEdit(destinationDoc.getLineOffset(line), content));
				}
			}
		} catch (CoreException e) {
			e.printStackTrace();
		} catch (BadLocationException e) {
			e.printStackTrace();
		}

		if (multiEdit.hasChildren()) {
			TextFileChange change = new TextFileChange(JavaCore.removeJavaLikeExtension(destinationFile.getName()), destinationFile);
			change.initializeValidationData(null);
			change.setTextType("java");
			change.setEdit(multiEdit);
			changes.add(change);
		}
		return status;
	}

	private IFile createNewDestinationFileIfNotExist() {
		final IFolder featureFolder = featureProject.getSourceFolder().getFolder(destinationFeature.getName());

		final String fileName = getDestinationFileName();
		String pack = "";
		if (!selectedElement.getPackage().startsWith(".")) pack = File.separator;

		pack = pack + selectedElement.getPackage().replaceAll("\\.", File.separator);
		File folder = new File(featureFolder.getRawLocation().toOSString() + pack);
		if (!folder.exists()) folder.mkdirs();

		try {
			featureProject.getSourceFolder().getFolder(featureFolder.getRawLocation().toOSString() + pack).refreshLocal(IResource.DEPTH_ONE, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}

		File destinationFile = new File(folder + File.separator + fileName);
		if (!destinationFile.exists()) destinationFile = createNewFeatureFile(destinationFile);

		return RefactoringUtil.getFile(destinationFile.getAbsolutePath());
	}

	private File createNewFeatureFile(File destinationFile) {
		try {
			String content = getNewFeatureFileContent();
			destinationFile.createNewFile();

			BufferedWriter writer = new BufferedWriter(new FileWriter(destinationFile, true));
			writer.write(content);
			writer.close();

			try {
				RefactoringUtil.getFile(destinationFile.getAbsolutePath()).refreshLocal(IResource.DEPTH_ONE, null);
			} catch (CoreException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
//			IProject project = featureProject.getProject();
//			project.refreshLocal(IResource.DEPTH_INFINITE, null);

			return destinationFile;
		} catch (IOException e) {
			e.printStackTrace();
		}
		return null;
	}

	private String getNewFeatureFileContent() {
		final IComposerExtensionClass composer = featureProject.getComposer();
		final String template = getJavaTemplate(composer);
		final String featureName = destinationFeature.getName();
		final String fileName = getDestinationFileName();
		final String className = fileName.substring(0, fileName.lastIndexOf("."));

		String classPattern = className;
		classPattern += getExtends(selectedElement.getExtendList(), " extends ");
		classPattern += getExtends(selectedElement.getImplementList(), " implements ");

		String contents = composer.replaceSourceContentMarker(template, false, selectedElement.getPackage());
		contents = contents.replaceAll(IComposerExtensionClass.CLASS_NAME_PATTERN, classPattern);
		contents = contents.replaceAll(IComposerExtensionClass.FEATUE_PATTER, featureName);
		return contents;
	}

	private String getExtends(HashSet<String> extendlist, String keyword) {
		String result = "";
		if (extendlist.size() > 0) result += keyword;

		String allExtends = "";
		for (String extend : extendlist) {
			if (!allExtends.isEmpty()) allExtends += ", ";
			allExtends += extend;
		}

		result += allExtends;

		return result;
	}

	private IFile getDestinationFile() {
		return createNewDestinationFileIfNotExist();
	}

	private String getDestinationFileName() {
		return file.substring(file.lastIndexOf(File.separator) + 1);
	}

	private String getJavaTemplate(IComposerExtensionClass composer) {
		for (String[] template : composer.getTemplates()) {
			if (template[0].equals("Java")) return template[2];

		}
		return null;
	}

	private RefactoringStatus createDeleteChanges() {

		RefactoringStatus status = new RefactoringStatus();
		MultiTextEdit multiEdit;

		if (deletableSignatures.size() == 0) return status;

		Map<IFile, MultiTextEdit> textEdits = new HashMap<>();

		int destinationFeatureId = featureProject.getProjectSignatures().getFeatureID(destinationFeature.getName());
		for (ExtendedPullUpSignature extendedSignature : deletableSignatures) {
			final int featureId = extendedSignature.getFeatureId();
			if (destinationFeatureId == featureId) continue;

			final AbstractSignature signature = extendedSignature.getSignature();
			final boolean isClassSignature = signature instanceof FujiClassSignature;
			final AFeatureData featureData = getFeatureDataForId(signature, featureId);
			if (featureData == null) continue;

			IFile pullUpFile = RefactoringUtil.getFile(featureData.getAbsoluteFilePath());

			if (textEdits.containsKey(pullUpFile)) multiEdit = textEdits.get(pullUpFile);
			else multiEdit = new MultiTextEdit();

			IDocumentProvider pullUpProvider = new TextFileDocumentProvider();
			try {
				pullUpProvider.connect(pullUpFile);
				final IDocument pullUpDoc = pullUpProvider.getDocument(pullUpFile);

				final String featureName = featureProject.getProjectSignatures().getFeatureName(featureId);
				if (isClassSignature) {
					if (featureName.equals(sourceFeature.getName())) continue;

					DeleteResourceChange deleteChange = new DeleteResourceChange(pullUpFile.getFullPath(), true);
					changes.add(deleteChange);
				} else {
					textEdits.put(pullUpFile, multiEdit);
					SignaturePosition position = featureData.getSigPosition();

					int startOffset = pullUpDoc.getLineOffset(position.getStartRow() - 1);
					int endOffset = pullUpDoc.getLineOffset(position.getEndRow() - 1) + position.getEndColumn();

					if (signature instanceof FujiFieldSignature) {
						int line = pullUpDoc.getLineOfOffset(startOffset);
						int length = pullUpDoc.getLineLength(line) - 1;
						String content = pullUpDoc.get(startOffset, length);

						final Set<AbstractSignature> fieldSignaturesOfLine = getFieldSignaturesOfLine(featureData);
						final Set<AbstractSignature> matchedFieldSignatures = getMatchedSignatureForLine(featureData, signature);

						if (matchedFieldSignatures.size() == 1
							|| (fieldSignaturesOfLine.size() == matchedFieldSignatures.size() && fieldSignaturesOfLine.containsAll(matchedFieldSignatures))) {
							DeleteEdit deleteEdit = new DeleteEdit(startOffset, length);
							if (!coversEdit(multiEdit, deleteEdit)) multiEdit.addChild(deleteEdit);
						} else {
							for (AbstractSignature fieldSignature : fieldSignaturesOfLine) {
								final AFeatureData fieldFeatureData = getFeatureDataForId(fieldSignature, featureId);
								final SignaturePosition sigPosition = fieldFeatureData.getSigPosition();
								final int startColumn = sigPosition.getIdentifierStart();
								int offset = pullUpDoc.getLineOffset(sigPosition.getStartRow() - 1);

								int replaceLength = sigPosition.getIdentifierEnd() - startColumn + 1;

								int separatorAfter = content.indexOf(",", startColumn);
								int separatorBefore = content.lastIndexOf(",", startColumn);
								if (separatorAfter > 0) {
									offset += startColumn - 1;
									replaceLength += separatorAfter - sigPosition.getIdentifierEnd() + 1;
								} else if (separatorBefore > 0) {
									offset += separatorBefore;
									replaceLength += startColumn - separatorBefore - 1;
								}

								multiEdit.addChild(new ReplaceEdit(offset, replaceLength, ""));
							}
						}
//						addEditChild(multiEdit, startOffset, endOffset);
					} else {
						int length = endOffset - startOffset;
						multiEdit.addChild(new DeleteEdit(startOffset, length));
					}
				}

			} catch (CoreException e) {
				e.printStackTrace();
			} catch (BadLocationException e) {
				e.printStackTrace();
			}
		}

		for (Entry<IFile, MultiTextEdit> entry : textEdits.entrySet()) {
			TextFileChange change = new TextFileChange(JavaCore.removeJavaLikeExtension(entry.getKey().getName()), entry.getKey());
			change.initializeValidationData(null);
			change.setTextType("java");
			change.setEdit(entry.getValue());
			changes.add(change);
		}

		return status;
	}

	private boolean coversEdit(MultiTextEdit multiEdit, DeleteEdit deleteEdit) {
		for (TextEdit textEdit : multiEdit.getChildren()) {
			if (textEdit.covers(deleteEdit)) return true;
		}
		return false;
	}

	private Set<AbstractSignature> getMatchedSignatureForLine(AFeatureData featureData, AbstractSignature signature) {
		Set<AbstractSignature> matchedSignaturesForClass =
			RefactoringUtil.getMatchedSignaturesForClass(signature.getParent().getFields(), featureData.getAbsoluteFilePath());
		Set<AbstractSignature> result = new HashSet<>();

		for (AbstractSignature abstractSignature : matchedSignaturesForClass) {
			final AFeatureData featureData2 = getFeatureDataForId(abstractSignature, featureData.getID());
			if (featureData.getID() == featureData2.getID()) {
				final AFeatureData extFeatureData = getFeatureDataForId(abstractSignature, featureData2.getID());
				if (extFeatureData.getSigPosition().getStartRow() == featureData.getSigPosition().getStartRow()
					&& extFeatureData.getSigPosition().getEndRow() == featureData.getSigPosition().getEndRow()) {
					result.add(abstractSignature);
				}
			}

		}

		return result;
	}

	private Set<AbstractSignature> getFieldSignaturesOfLine(AFeatureData featureData) {

		Set<AbstractSignature> result = new HashSet<>();
		for (ExtendedPullUpSignature extSignature : deletableSignatures) {

			final int featureId = extSignature.getFeatureId();
			final AbstractSignature signature = extSignature.getSignature();
			if (featureId == featureData.getID() && signature instanceof FujiFieldSignature) {
				final AFeatureData extFeatureData = getFeatureDataForId(signature, featureId);
				if (extFeatureData.getSigPosition().getStartRow() == featureData.getSigPosition().getStartRow()
					&& extFeatureData.getSigPosition().getEndRow() == featureData.getSigPosition().getEndRow()) {
					result.add(extSignature.getSignature());
				}
			}
		}
		return result;
	}

	private void addEditChild(final MultiTextEdit multiEdit, final int startOffset, final int endOffset) {

		for (TextEdit deleteEdit : multiEdit.getChildren()) {

			TextEdit createdEdit = null;

			if (startOffset >= deleteEdit.getOffset() && endOffset > deleteEdit.getExclusiveEnd())
				createdEdit = new DeleteEdit(deleteEdit.getOffset(), endOffset - startOffset);
			else if (startOffset < deleteEdit.getOffset() && endOffset <= deleteEdit.getExclusiveEnd())
				createdEdit = new DeleteEdit(startOffset, deleteEdit.getLength());
			else if (startOffset < deleteEdit.getOffset() && endOffset > deleteEdit.getExclusiveEnd())
				createdEdit = new DeleteEdit(startOffset, endOffset - startOffset);

			if (createdEdit != null) {
				multiEdit.removeChild(deleteEdit);
				multiEdit.addChild(createdEdit);
				return;
			}
		}

		multiEdit.addChild(new DeleteEdit(startOffset, endOffset - startOffset));
	}
}
