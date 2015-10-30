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
import org.eclipse.jdt.internal.corext.refactoring.nls.changes.CreateTextFileChange;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.resource.MoveResourceChange;
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
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.SignaturePosition;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class PullUpRefactoring extends Refactoring {

	private final IFeatureProject featureProject;
	private final AbstractClassSignature selectedElement;
	private final String file;
	private final Feature sourceFeature;
	private final Map<AbstractSignature, List<Feature>> clonedSignatures;
	private Feature destinationFeature;
	private Set<ExtendedPullUpSignature> pullUpSignatures;
	private Set<ExtendedPullUpSignature> deletableSignatures;
	private List<Change> changes;
	

	private static final String EXIST_ELEMENT_IN_FEATURE = "A {0} ''{1}'' with this name already exists in feature ''{2}''.";
	
	@Override
	public String getName() {
		return "PullUp";
	}
	
	public PullUpRefactoring(AbstractClassSignature selection, IFeatureProject featureProject, String file) {
		this.selectedElement = selection;
		this.featureProject = featureProject;
		this.file = file;
		this.sourceFeature = determineSourceFeature();
		this.clonedSignatures = (new CloneSignatureMatcher(featureProject, selectedElement, file)).computeClonedSignatures();;
	}
	
	private Feature determineSourceFeature() {
		final AFeatureData featureData = getFeatureDataForFile(selectedElement, file);
		if (featureData == null) return null;
		
		final ProjectSignatures projectSignatures = featureProject.getProjectSignatures();
		final String featureName = projectSignatures.getFeatureName(featureData.getID());
		return projectSignatures.getFeatureModel().getFeature(featureName);
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
	
	public Feature getSourceFeature() {
		return sourceFeature;
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
	
	public Map<AbstractSignature, List<Feature>> getClonedSignatures() {
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
	
	public List<Feature> getFeatureCandidates() {
		
		final List<Feature> features = new ArrayList<>();
		
		if (sourceFeature == null) return features; 
		
		Feature parentFeature = sourceFeature.getParent();
		
		while(parentFeature != null)
		{
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
		
		final Set<AbstractSignature> matchedSignatures = RefactoringUtil.getIncludedMatchingSignaturesForFile(selectedElement, getDestinationFile().getRawLocation().toOSString());
		
		for (ExtendedPullUpSignature extendedPullUpSignature : pullUpSignatures) {
			
			final AbstractSignature signature = extendedPullUpSignature.getSignature();
			if (existSignature(signature, matchedSignatures)) 
			{	
				String type;
				if (signature instanceof AbstractMethodSignature)
					type = "method";
				else if (signature instanceof AbstractFieldSignature)
					type = "field";
				else
					type = "class";
				
				String msg = Messages.format(EXIST_ELEMENT_IN_FEATURE, new String[] {type, signature.getName(), destinationFeature.getName()});
				refactoringStatus.addError(msg);
			}
		}
		
		return refactoringStatus;
	}
	
	private boolean existSignature(final AbstractSignature pullUpSignature, final Set<AbstractSignature> matchedSignatures) {
		
		for (AbstractSignature abstractSignature : matchedSignatures) {
			if (!abstractSignature.getClass().equals(pullUpSignature.getClass())) continue;
		    
		    if ((abstractSignature instanceof FujiMethodSignature) && existSignature((FujiMethodSignature) abstractSignature, (FujiMethodSignature) pullUpSignature))
				return true;
			
			if (((abstractSignature instanceof FujiFieldSignature) || (abstractSignature instanceof FujiClassSignature)) && existSignature(abstractSignature, pullUpSignature)) 
				return true;
		}
		return false;
	}
	
	private boolean existSignature(final AbstractSignature sig1, final AbstractSignature sig2) {
		if (sig1.equals(sig2))
			return isCodeClone(sig2);
		else
			return (RefactoringUtil.hasSameName(sig1, sig2) && !sig1.equals(sig2));
	}
	
	private boolean existSignature(final FujiMethodSignature method1, final FujiMethodSignature method2) {
		if (method1.equals(method2))
			return isCodeClone(method1);
		else
			return RefactoringUtil.hasSameName(method1, method2) && RefactoringUtil.hasSameParameters(method1, method2) && RefactoringUtil.hasSameReturnType(method1, method2);
	}

	private boolean isCodeClone(final AbstractSignature signature){
		
		if (!clonedSignatures.containsKey(signature)) return false;

		return !clonedSignatures.get(signature).contains(destinationFeature);
	}
	
	@Override
	public Change createChange(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		try {
			pm.beginTask("Creating change...", 1);

//			createNewDestinationFileIfNotExist();
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
			
			int destinationFeatureId  = featureProject.getProjectSignatures().getFeatureID(destinationFeature.getName());

			for (ExtendedPullUpSignature extendedSignature : pullUpSignatures) {
				
				final AbstractSignature signature = extendedSignature.getSignature(); 
				
				AFeatureData featureData = getFeatureDataForId(signature, destinationFeatureId);
				if (featureData != null) continue;
				
				featureData = getFeatureDataForFile(signature, file);			
				if (featureData == null) continue;
				
				AbstractSignature parent;
				if (signature instanceof FujiClassSignature)
				{
					MoveResourceChange moveChange = new MoveResourceChange(pullUpFile, destinationFile.getParent());
					changes.add(moveChange);
				}
				else
				{
					if (!destinationFile.exists())
					{
						String content = getNewFeatureFileContent();
						
						CreateTextFileChange createChange = new CreateTextFileChange(destinationFile.getFullPath(), content, pullUpFile.getCharset(), "java");
						changes.add(createChange);
						destinationDoc.set(getNewFeatureFileContent());
					}
					
					parent = signature.getParent();
					final AFeatureData destinationFeatureData = getFeatureDataForFile(parent, destinationFile.getRawLocation().toOSString());
				
					SignaturePosition position = featureData.getSigPosition();
				
					int startOffset = pullUpDoc.getLineOffset(position.getStartRow() - 1) ;
					int endOffset = pullUpDoc.getLineOffset(position.getEndRow() - 1) + position.getEndColumn();
					String content = pullUpDoc.get(startOffset, endOffset-startOffset) + "\n";
				
					int line = destinationDoc.getNumberOfLines() - 1;
					if (destinationFeatureData != null)
						line = destinationFeatureData.getSigPosition().getEndRow()-1;
					
					multiEdit.addChild(new InsertEdit(destinationDoc.getLineOffset(line), content));
				}
			}
		} catch (CoreException e) {
			e.printStackTrace();
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
		
		if (multiEdit.hasChildren())
		{
			TextFileChange change = new TextFileChange(JavaCore.removeJavaLikeExtension(destinationFile.getName()), destinationFile);
			change.initializeValidationData(null);
			change.setTextType("java");
			change.setEdit(multiEdit);
			changes.add(change);
		}
		return status;
	}

	private void createNewDestinationFileIfNotExist() {
		
		IFile destinationFile = getDestinationFile();
		
		if (destinationFile.exists()) 
			return;
		
		createNewFeatureFile();
	}

	private void createNewFeatureFile() {
		IFile destinationFile =  null;
		try {
			String content = getNewFeatureFileContent();
			InputStream stream = new ByteArrayInputStream(content.getBytes(Charset.availableCharsets().get("UTF-8")));
			
			destinationFile = getDestinationFile();
			destinationFile.create(stream, true, new NullProgressMonitor());
			stream.close();
		} catch (IOException | CoreException e) {
			e.printStackTrace();
		}
	}

	private String getNewFeatureFileContent() {
		final IComposerExtensionClass composer = featureProject.getComposer();
		final String template = getJavaTemplate(composer);
		final String featureName = destinationFeature.getName();
		final String fileName = getDestinationFileName();
		final String className = fileName.substring(0, fileName.lastIndexOf("."));
		
		String contents = composer.replaceSourceContentMarker(template, false, selectedElement.getPackage());
		contents = contents.replaceAll(IComposerExtensionClass.CLASS_NAME_PATTERN, className);
		contents = contents.replaceAll(IComposerExtensionClass.FEATUE_PATTER, featureName);
		return contents;
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
		
		int destinationFeatureId  = featureProject.getProjectSignatures().getFeatureID(destinationFeature.getName());
		for (ExtendedPullUpSignature signature : deletableSignatures) {
			if (destinationFeatureId == signature.getFeatureId()) continue;
			
			final AFeatureData featureData = getFeatureDataForId(signature.getSignature(), signature.getFeatureId());
			if (featureData == null) continue;
			
			IFile pullUpFile = RefactoringUtil.getFile(featureData.getAbsoluteFilePath());
			
			if (textEdits.containsKey(pullUpFile))
				multiEdit = textEdits.get(pullUpFile);
			else
				multiEdit = new MultiTextEdit();

			IDocumentProvider pullUpProvider = new TextFileDocumentProvider();
			try {
				pullUpProvider.connect(pullUpFile);
				final IDocument pullUpDoc = pullUpProvider.getDocument(pullUpFile);

				final String featureName = featureProject.getProjectSignatures().getFeatureName(signature.getFeatureId());
				if (signature.getSignature() instanceof FujiClassSignature && featureName.equals(sourceFeature.getName()))  continue;
							
				textEdits.put(pullUpFile, multiEdit);
				SignaturePosition position = featureData.getSigPosition();
			
				int startOffset = pullUpDoc.getLineOffset(position.getStartRow() - 1) ;
				int endOffset = pullUpDoc.getLineOffset(position.getEndRow() - 1) + position.getEndColumn();
			
				multiEdit.addChild(new DeleteEdit(startOffset, endOffset - startOffset));
				
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
