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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.DeleteEdit;
import org.eclipse.text.edits.InsertEdit;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;
import org.eclipse.ui.texteditor.IDocumentProvider;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.SignaturePosition;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public class PullUpMethodRefactoring extends PullUpRefactoring<FujiMethodSignature> {
	
	private List<Change> changes;

	public PullUpMethodRefactoring(FujiMethodSignature selection, IFeatureProject featureProject, String file) {
		super(selection, featureProject, file);
	}

	@Override
	public String getName() {
		return "PullUp";
	}
	
	@Override
	public FujiMethodSignature[] getPullableElements() {
		final Set<AbstractMethodSignature> result = new HashSet<>();
		final Set<AbstractMethodSignature> methods = selectedElement.getParent().getMethods();
		for (AbstractMethodSignature abstractMethodSignature : methods) {
			for (AFeatureData featureData : abstractMethodSignature.getFeatureData()) {
				if (featureData.getAbsoluteFilePath().equals(file)) {
					result.add(abstractMethodSignature);
					break;
				}
			}
		}
		return result.toArray(new FujiMethodSignature[methods.size()]);
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
			refactoringStatus.merge(createInsertChanges());
			refactoringStatus.merge(createDeleteChanges());

		} finally {
			pm.done();
		}
		return refactoringStatus;
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
		
		if (pullUpSignatures.length == 0)
			return status;
		
		IFile pullUpFile = RefactoringUtil.getFile(file);
		AFeatureData destinationFeatureData = getFeatureDataForId(destinationType.getSignature(), destinationType.getFeatureId());
		IFile destinationFile = RefactoringUtil.getFile(destinationFeatureData.getAbsoluteFilePath());

		IDocumentProvider pullUpProvider = new TextFileDocumentProvider();
		IDocumentProvider destinationProvider = new TextFileDocumentProvider();
		try {
			pullUpProvider.connect(pullUpFile);
			destinationProvider.connect(destinationFile);
			final IDocument pullUpDoc = pullUpProvider.getDocument(pullUpFile);
			final IDocument destinationDoc = destinationProvider.getDocument(destinationFile);
			
			for (AbstractSignature signature : pullUpSignatures) {
				final AFeatureData featureData = getFeatureDataForFile(signature, file);
				
				if (featureData == null) continue;
				
				SignaturePosition position = featureData.getSigPosition();
				
				int startOffset = pullUpDoc.getLineOffset(position.getStartRow() - 1) ;
				int endOffset = pullUpDoc.getLineOffset(position.getEndRow() - 1) + position.getEndColumn();
				String content = "\n" + pullUpDoc.get(startOffset, endOffset-startOffset) + "\n";
				
				multiEdit.addChild(new InsertEdit(destinationDoc.getLineOffset(destinationDoc.getNumberOfLines()-1), content));
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
	
	private RefactoringStatus createDeleteChanges() {

		RefactoringStatus status = new RefactoringStatus();
		MultiTextEdit multiEdit;
		
		if (pullUpSignatures.length == 0)
			return status;
		
		Map<IFile, MultiTextEdit> textEdits = new HashMap<>();
		
		for (ExtendedPullUpSignature signature : deletedMethods) {
			
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
	
	private AFeatureData getFeatureDataForFile(final AbstractSignature signature, final String file){
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getAbsoluteFilePath().equals(file)) return featureData;
		}
		return null;
	}
	
	private AFeatureData getFeatureDataForId(final AbstractSignature signature, final int featureId){
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getID() == featureId) return featureData;
		}
		return null;
	}

	
}