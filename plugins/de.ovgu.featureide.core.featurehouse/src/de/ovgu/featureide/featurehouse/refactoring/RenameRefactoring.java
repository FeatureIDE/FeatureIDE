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
package de.ovgu.featureide.featurehouse.refactoring;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBuffer;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.JavaConventions;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.rewrite.ASTRewrite;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.TextEdit;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public abstract class RenameRefactoring<T extends IMember> extends Refactoring {

	protected final IFeatureProject featureProject;
	protected final T renamingElement;
	protected ProjectSignatures signatures;
	protected String newName;
	private Map<ICompilationUnit, TextFileChange> changes = new LinkedHashMap<ICompilationUnit, TextFileChange>();
	private Map<ICompilationUnit, List<ASTRewrite>> rewrites = new LinkedHashMap<ICompilationUnit, List<ASTRewrite>>();

	public RenameRefactoring(T selection, IFeatureProject featureProject) {
		this.renamingElement = selection;
		this.featureProject = featureProject;
		this.newName = renamingElement.getElementName();
	}

	public void setNewName(String newName) {
		this.newName = newName;
	}

	public String getNewName() {
		return this.newName;
	}

	protected abstract boolean checkSignature(AbstractSignature signature);

	protected abstract IASTVisitor getASTVisitor(AbstractSignature signature);

	//	protected abstract IASTVisitor getASTVisitor2(AbstractSignature signature);
	protected abstract boolean checkPreConditions(RefactoringStatus refactoringStatus);

	@Override
	public RefactoringStatus checkInitialConditions(final IProgressMonitor pm) throws CoreException, OperationCanceledException {
		RefactoringStatus refactoringStatus = new RefactoringStatus();

		try {
			pm.beginTask("Checking preconditions...", 1);

			// die Methode existiert
			if (!renamingElement.exists())
				refactoringStatus.merge(RefactoringStatus.createFatalErrorStatus(MessageFormat.format("Element ''{0}'' does not exist.",
						new Object[] { renamingElement.getElementName() })));
			// ob die Methode nicht aus einer binaeren Klasse (.class File) stammt und die Klassendatei keine Compile-Fehler aufweist
			else {
				if (!renamingElement.isBinary() && !renamingElement.getCompilationUnit().isStructureKnown())
					refactoringStatus.merge(RefactoringStatus.createFatalErrorStatus(MessageFormat.format("Compilation unit ''{0}'' contains compile errors.",
							new Object[] { renamingElement.getCompilationUnit().getElementName() })));
			}

			if ("".equals(newName))
				return RefactoringStatus.createFatalErrorStatus("Hier neuen Methodennamen eingeben");

			if (renamingElement.getElementName().equals(newName))
				return refactoringStatus;

			IStatus status = JavaConventions.validateMethodName(newName, JavaCore.VERSION_1_7, JavaCore.VERSION_1_7);

			if (!status.isOK()) {
				switch (status.getSeverity()) {
				case IStatus.ERROR:
					refactoringStatus.merge(RefactoringStatus.createFatalErrorStatus(status.getMessage()));
					break;
				case IStatus.WARNING:
					refactoringStatus.merge(RefactoringStatus.createWarningStatus(status.getMessage()));
					break;
				case IStatus.INFO:
					refactoringStatus.merge(RefactoringStatus.createInfoStatus(status.getMessage()));

				}
			}

		} finally {
			pm.done();
		}

		return refactoringStatus;
	}

	@Override
	public final RefactoringStatus checkFinalConditions(final IProgressMonitor pm) throws CoreException, OperationCanceledException {
		final RefactoringStatus refactoringStatus = new RefactoringStatus();
		try {
			pm.beginTask("Checking preconditions...", 2);

			ExtendedFujiSignaturesJob efsj = new ExtendedFujiSignaturesJob(featureProject);
			efsj.schedule();
			efsj.join();

			// pruefen, ob neues Element schon existiert

			signatures = featureProject.getFSTModel().getProjectSignatures();
			if (signatures == null)
				return refactoringStatus;

			final FSTModel model = featureProject.getFSTModel();
			if (model == null)
				return refactoringStatus;

			if (!checkPreConditions(refactoringStatus))
				return refactoringStatus;

			final SignatureIterator iter = signatures.iterator();
			while (iter.hasNext()) {
				final AbstractSignature signature = iter.next();
				//				if (!(signature instanceof FujiMethodSignature)) continue;
				//				FujiMethodSignature methodSignature = (FujiMethodSignature) signature;
				////				System.out.println(Flags.toString(renamingElement.getFlags()));
				doMagic(signature);
			}
			for (Entry<ICompilationUnit, List<ASTRewrite>> entry : rewrites.entrySet()) {
				rewriteAST(entry.getKey(), entry.getValue());
			}

		} catch (InterruptedException e) {
			e.printStackTrace();
		} finally {
			pm.done();
		}
		return refactoringStatus;
	}

	private void doMagic(final AbstractSignature signature) throws JavaModelException {

		final FOPFeatureData[] featureData = (FOPFeatureData[]) signature.getFeatureData();
		for (int j = 0; j < featureData.length; j++) {
			final FOPFeatureData fopFeature = featureData[j];
			final IFile file = fopFeature.getFile();

			if (checkSignature(signature)) {

				rewriteAST(signature, file, getInvokedSignaturesList(fopFeature.getInvokedSignatures()));
			}
		}
		
	}

	private Map<AbstractSignature, IFile> getInvokedSignaturesList(List<AbstractSignature> invokedSignatures) throws JavaModelException {
		Map<AbstractSignature, IFile> result = new HashMap<>();
		for (AbstractSignature signature : invokedSignatures) {
			final FOPFeatureData featureData = (FOPFeatureData) signature.getFirstFeatureData();
			if (featureData == null)
				continue;

			result.put(signature, featureData.getFile());
		}
		return result;
	}

	private void rewriteAST(final AbstractSignature signature, final IFile file, final Map<AbstractSignature, IFile> invokedSignatures)
			throws JavaModelException {

		MethodVisitor visitor = new MethodVisitor((FujiMethodSignature) signature, file, invokedSignatures);
		visitor.startVisit();

		Map<ICompilationUnit, List<ASTNode>> changingUnits = visitor.getChangingNodes();

		for (Entry<ICompilationUnit, List<ASTNode>> changingUnit : changingUnits.entrySet()) {

			final ICompilationUnit unit = changingUnit.getKey();
			List<ASTRewrite> listAstRewrite;
			if (rewrites.containsKey(unit)) {
				listAstRewrite = rewrites.get(unit);
			} else {
				listAstRewrite = new ArrayList<>();
				rewrites.put(unit, listAstRewrite);
			}

			for (ASTNode astNode : changingUnit.getValue()) {
				ASTRewrite astRewrite = ASTRewrite.create(astNode.getRoot().getAST());
				listAstRewrite.add(astRewrite);
				rewriteMethodDeclaration(astRewrite, astNode);
			}
		}
	}

	@Override
	public final Change createChange(IProgressMonitor pm) throws CoreException, OperationCanceledException {

		try {
			pm.beginTask("Creating change...", 1);

			final Collection<TextFileChange> textFileChanges = changes.values();
			return new CompositeChange(getName(), textFileChanges.toArray(new Change[textFileChanges.size()]));
		} finally {
			pm.done();
		}
	}

	private void rewriteMethodDeclaration(ASTRewrite astRewrite, ASTNode oldNode) throws JavaModelException {
		AST ast = oldNode.getAST();

		ASTNode newNode = null;
		if (oldNode instanceof MethodDeclaration) {
			newNode = (MethodDeclaration) ASTNode.copySubtree(ast, oldNode);
			((MethodDeclaration) newNode).setName(ast.newSimpleName(newName));
		} else if (oldNode instanceof MethodInvocation) {
			newNode = (MethodInvocation) ASTNode.copySubtree(ast, oldNode);
			((MethodInvocation) newNode).setName(ast.newSimpleName(newName));
		}
		if (newNode != null)
			astRewrite.replace(oldNode, newNode, null);
	}

	protected boolean hasSameName(final String signatureName, final String otherName) {
		return signatureName.equals(otherName);
	}

	protected boolean hasSameClass(final AbstractSignature signature) {
		return getClassforSiganture(signature).equals(renamingElement.getDeclaringType().getFullyQualifiedName());
	}

	private String getClassforSiganture(final AbstractSignature signature) {
		AbstractClassSignature parent = signature.getParent();
		if (parent != null)
			return parent.getName();

		return signature.getName();
	}

	protected void rewriteAST(ICompilationUnit unit, List<ASTRewrite> astRewrite) {
		try {
			ITextFileBuffer buffer = acquire(unit);
			if (buffer == null)
				return;

			MultiTextEdit multiEdit = new MultiTextEdit();
			TextFileChange change = null;
			for (ASTRewrite astRewrite2 : astRewrite) {

				TextEdit edit = astRewrite2.rewriteAST(buffer.getDocument(), null);
				multiEdit.addChild(edit);
			}

			if (!multiEdit.hasChildren())
				return;

			change = new TextFileChange(unit.getElementName(), (IFile) unit.getResource());
			change.setTextType("java");
			change.setEdit(multiEdit);

			changes.put(unit, change);
		} catch (CoreException exception) {
			exception.printStackTrace();
		}
	}

	private ITextFileBuffer acquire(final ICompilationUnit unit) throws CoreException {
		final IResource resource = unit.getResource();
		if (resource != null && resource.getType() == IResource.FILE) {
			final IPath path = resource.getFullPath();
			FileBuffers.getTextFileBufferManager().connect(path, LocationKind.IFILE, new NullProgressMonitor());
			return FileBuffers.getTextFileBufferManager().getTextFileBuffer(path, LocationKind.IFILE);
		}
		return null;
	}

}
