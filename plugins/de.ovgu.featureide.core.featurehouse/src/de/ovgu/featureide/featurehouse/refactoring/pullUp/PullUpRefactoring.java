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

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.DeleteEdit;
import org.eclipse.text.edits.InsertEdit;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;
import org.eclipse.ui.texteditor.IDocumentProvider;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.SignaturePosition;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class PullUpRefactoring extends Refactoring {

	protected final IFeatureProject featureProject;
	protected final AbstractClassSignature selectedElement;
	protected final String file;
	protected Feature destinationFeature;
	protected Set<ExtendedPullUpSignature> pullUpSignatures;
	protected Set<ExtendedPullUpSignature> deletableSignatures;
	
	private List<Change> changes;

	@Override
	public String getName() {
		return "PullUp";
	}
	
	public PullUpRefactoring(AbstractClassSignature selection, IFeatureProject featureProject, String file) {
		this.selectedElement = selection;
		this.featureProject = featureProject;
		this.file = file;
	}
	
	public List<Feature> getCandidateTypes(final RefactoringStatus status) {
		
		final List<Feature> features = new ArrayList<>();
		
		final AFeatureData featureData = getFeatureDataForFile(selectedElement, file);
		if (featureData == null) return null;
		
		final ProjectSignatures projectSignatures = featureProject.getProjectSignatures();
		final String featureName = projectSignatures.getFeatureName(featureData.getID());
		final Feature feature = projectSignatures.getFeatureModel().getFeature(featureName);
		if (feature == null) return null; 
		
		Feature parentFeature = feature.getParent();
		
		while(parentFeature != null)
		{
			if (parentFeature.isConcrete()) features.add(0, parentFeature);
			parentFeature = parentFeature.getParent();
		}
		return features;
	}
	

	protected AFeatureData getFeatureDataForFile(final AbstractSignature signature, final String file){
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getAbsoluteFilePath().equals(file)) return featureData;
		}
		return null;
	}
	
	protected AFeatureData getFeatureDataForId(final AbstractSignature signature, final int featureId){
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getID() == featureId) return featureData;
		}
		return null;
	}

	public void setDestinationFeature(Feature destinationFeature) {
		this.destinationFeature = destinationFeature;
	}
	
	public Feature getDestinationFeature() {
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
	
	public Set<ExtendedPullUpSignature> getPullableElements() {
		final Set<ExtendedPullUpSignature> result = new HashSet<>();
		addPullableSignature(result, selectedElement);
		addPullableSignatures(result, selectedElement.getMethods());
		addPullableSignatures(result, selectedElement.getFields());
		return result;
	}

	private void addPullableSignatures(final Set<ExtendedPullUpSignature> result, final Set<? extends AbstractSignature> signatures) {
		for (AbstractSignature abstractSignature : signatures) {
			addPullableSignature(result, abstractSignature);
		}
	}

	private void addPullableSignature(final Set<ExtendedPullUpSignature> result, AbstractSignature abstractSignature) {
		for (AFeatureData featureData : abstractSignature.getFeatureData()) {
			if (featureData.getAbsoluteFilePath().equals(file)) {
				result.add(new ExtendedPullUpSignature(abstractSignature, featureData.getID()));
				break;
			}
		}
	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor pm) throws CoreException, OperationCanceledException {	
		RefactoringStatus status = new RefactoringStatus();
		return status;
	}
	

	@Override
	public RefactoringStatus checkFinalConditions(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		final RefactoringStatus refactoringStatus = new RefactoringStatus();

		try {
			pm.beginTask("Checking preconditions...", 2);

			changes = new ArrayList<Change>();
			
			refactoringStatus.merge(createNewDestinationFileIfNotExist());
			if (refactoringStatus.hasError()) return refactoringStatus;
			
			refactoringStatus.merge(checkIfPullUpSignaturesExistInFeature());
			if (refactoringStatus.hasError()) return refactoringStatus;
			
			
			refactoringStatus.merge(createInsertChanges());
			refactoringStatus.merge(createDeleteChanges());

		} finally {
			pm.done();
		}
		return refactoringStatus;
	}

	private boolean existClassInDestinationFeature() {
		
		return false;
	}

	private RefactoringStatus checkIfPullUpSignaturesExistInFeature() {
		
//		final Set<AbstractSignature> matchedSignatures = RefactoringUtil.getIncludedMatchingSignaturesForFile(selectedElement, absoluteFileString);
		
//		for (ExtendedPullUpSignature extendedPullUpSignature : pullUpSignatures) {
//			destinationFeature
//		}
		
		return null;
	}

	private void getClassSignatureForDestinationFile() {
		
		for (AFeatureData featureData : selectedElement.getFeatureData()) {
			
		}
		
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
		
		if (pullUpSignatures.size() == 0)
			return status;
		
		IFile pullUpFile = RefactoringUtil.getFile(file);
		
		IFile destinationFile = getDestinationFile();
		
		IDocumentProvider pullUpProvider = new TextFileDocumentProvider();
		IDocumentProvider destinationProvider = new TextFileDocumentProvider();
		try {
			pullUpProvider.connect(pullUpFile);
			destinationProvider.connect(destinationFile);
			final IDocument pullUpDoc = pullUpProvider.getDocument(pullUpFile);
			final IDocument destinationDoc = destinationProvider.getDocument(destinationFile);
			
			for (ExtendedPullUpSignature extendedSignature : pullUpSignatures) {
				final AFeatureData featureData = getFeatureDataForFile(extendedSignature.getSignature(), file);
				
				if (featureData == null) continue;
				
				SignaturePosition position = featureData.getSigPosition();
				
				int startOffset = pullUpDoc.getLineOffset(position.getStartRow() - 1) ;
				int endOffset = pullUpDoc.getLineOffset(position.getEndRow() - 1) + position.getEndColumn();
				String content = "\n" + pullUpDoc.get(startOffset, endOffset-startOffset) + "\n";
				
				AbstractSignature parent;
				if (extendedSignature.getSignature() instanceof FujiClassSignature)
					parent = extendedSignature.getSignature();
				else
					parent = extendedSignature.getSignature().getParent();
					
				final AFeatureData destinationFeatureData = getFeatureDataForFile(parent, destinationFile.getRawLocation().toOSString());

				int line = destinationDoc.getNumberOfLines() - 1;
				if (destinationFeatureData != null)
					line = destinationFeatureData.getSigPosition().getEndRow()-1;
				
				multiEdit.addChild(new InsertEdit(destinationDoc.getLineOffset(line), content));
			}
		} catch (CoreException e) {
			e.printStackTrace();
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
		
		TextFileChange change = new TextFileChange(JavaCore.removeJavaLikeExtension(destinationFile.getName()), destinationFile);
		change.initializeValidationData(null);
		change.setTextType("java");
		change.setEdit(multiEdit);
		changes.add(change);
		return status;
	}
	
	private RefactoringStatus createNewDestinationFileIfNotExist() {
		
		IFile destinationFile = getDestinationFile();
		
		if (destinationFile.exists()) 
			return new RefactoringStatus();
		
		return createNewFeatureFile();
	}

	private RefactoringStatus createNewFeatureFile() {
		RefactoringStatus status = new RefactoringStatus();
		try {
			final IComposerExtensionClass composer = featureProject.getComposer();
			final String template = getJavaTemplate(composer);
			final String featureName = destinationFeature.getName();
			final String fileName = getDestinationFileName();
			final String className = fileName.substring(0, fileName.lastIndexOf("."));
			
			String contents = composer.replaceSourceContentMarker(template, false, selectedElement.getPackage());
			contents = contents.replaceAll(IComposerExtensionClass.CLASS_NAME_PATTERN, className);
			contents = contents.replaceAll(IComposerExtensionClass.FEATUE_PATTER, featureName);
			InputStream stream = new ByteArrayInputStream(contents.getBytes(Charset.availableCharsets().get("UTF-8")));
			
			IFile destinationFile = getDestinationFile();
			destinationFile.create(stream, true, new NullProgressMonitor());
			stream.close();
		} catch (IOException | CoreException e) {
			status.addError(e.getMessage());
		}
		return status;
	}

	private IFile getDestinationFile() {
		final IFolder featureFolder = featureProject.getSourceFolder().getFolder(destinationFeature.getName());
		final String fileName = getDestinationFileName();
		
		String pack = selectedElement.getPackage().replaceAll("\\.",File.separator) + File.separator;
		return featureFolder.getFile(pack + fileName);
	}

	private String getDestinationFileName() {
		return file.substring(file.lastIndexOf(File.separator) +1);
	}

	private String getJavaTemplate(IComposerExtensionClass composer) {
		for (String[] template :  composer.getTemplates()) {
			if (template[0].equals("Java")) 
				return template[2];
			
		}
		return null;
	}
	
	private RefactoringStatus createDeleteChanges() {

		RefactoringStatus status = new RefactoringStatus();
		MultiTextEdit multiEdit;
		
		if (deletableSignatures.size() == 0)
			return status;
		
		Map<IFile, MultiTextEdit> textEdits = new HashMap<>();
		
		for (ExtendedPullUpSignature signature : deletableSignatures) {
			
			final AFeatureData featureData = getFeatureDataForId(signature.getSignature(), signature.getFeatureId());
			if (featureData == null) continue;
			
			IFile pullUpFile = RefactoringUtil.getFile(featureData.getAbsoluteFilePath());
			
			if (textEdits.containsKey(pullUpFile))
				multiEdit = textEdits.get(pullUpFile);
			else
			{
				 multiEdit = new MultiTextEdit();
				 textEdits.put(pullUpFile, multiEdit);
			}

			IDocumentProvider pullUpProvider = new TextFileDocumentProvider();
			try {
				pullUpProvider.connect(pullUpFile);
				final IDocument pullUpDoc = pullUpProvider.getDocument(pullUpFile);
				
				SignaturePosition position = featureData.getSigPosition();
				
				int startOffset = pullUpDoc.getLineOffset(position.getStartRow() - 1) ;
				int endOffset = pullUpDoc.getLineOffset(position.getEndRow() - 1) + position.getEndColumn();
				
				multiEdit.addChild(new DeleteEdit(startOffset, endOffset - startOffset + 1));
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
	
}
