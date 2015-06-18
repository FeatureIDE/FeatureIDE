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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.JavaConventions;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public abstract class RenameRefactoring<T extends IMember, Q extends AbstractSignature> extends Refactoring {

	protected final IFeatureProject featureProject;
	protected final T renamingElement;
	protected ProjectSignatures signatures;
	protected String newName;
	private Map<ICompilationUnit, TextFileChange> changes = new LinkedHashMap<ICompilationUnit, TextFileChange>();
	private Map<String, AbstractClassSignature> classes = new HashMap<>();
	private Map<ICompilationUnit, List<SearchMatch>> nodes = new HashMap<>();

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

	protected abstract IASTVisitor getASTVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature);

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

			//			public final RefactoringStatus checkNewElementName(String newName) {
			//				Assert.isNotNull(newName, "new name"); //$NON-NLS-1$
			//
			//				RefactoringStatus status= Checks.checkName(newName, JavaConventionsUtil.validateMethodName(newName, fMethod));
			//				if (status.isOK() && !Checks.startsWithLowerCase(newName))
			//					status= RefactoringStatus.createWarningStatus(fIsComposite
			//							? Messages.format(RefactoringCoreMessages.Checks_method_names_lowercase2, new String[] { BasicElementLabels.getJavaElementName(newName), getDeclaringTypeLabel()})
			//							: RefactoringCoreMessages.Checks_method_names_lowercase);
			//
			//				if (Checks.isAlreadyNamed(fMethod, newName))
			//					status.addFatalError(fIsComposite
			//							? Messages.format(RefactoringCoreMessages.RenameMethodRefactoring_same_name2, new String[] { BasicElementLabels.getJavaElementName(newName), getDeclaringTypeLabel() } )
			//							: RefactoringCoreMessages.RenameMethodRefactoring_same_name,
			//							JavaStatusContext.create(fMethod));
			//				return status;
			//			}

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

			classes = getClasses();
			Set<AbstractSignature> matchedSignatures = getMatchedSignatures();

			AbstractSignature selectedSignature = null;
			if (matchedSignatures.size() == 1) {
				selectedSignature = matchedSignatures.iterator().next();
			} else {
				for (AbstractSignature matchedSignature : matchedSignatures) {
					if (hasSameClass(matchedSignature))
						selectedSignature = matchedSignature;
				}
			}

			if (selectedSignature != null) {
				Set<RefactoringSignature> involvedSignatures = getInvolvedSignatures(selectedSignature, matchedSignatures);

				for (RefactoringSignature refactoringSignature : involvedSignatures) {
					search(refactoringSignature);
				}

				for (Entry<ICompilationUnit, List<SearchMatch>> searchMatches : nodes.entrySet()) {
					rewriteAST(searchMatches.getKey(), searchMatches.getValue());
				}
			}

		} catch (InterruptedException e) {
			e.printStackTrace();
		} finally {
			pm.done();
		}
		return refactoringStatus;
	}

	private Set<RefactoringSignature> getInvolvedSignatures(AbstractSignature selectedSignature, Set<AbstractSignature> matchedSignatures) {
		Set<AbstractClassSignature> involvedClasses2 = new HashSet<>();

		addSubAndSuperClasses(involvedClasses2, selectedSignature.getParent());

		Set<RefactoringSignature> involvedClasses = createRefactoringSignatures(involvedClasses2, matchedSignatures);

		handleInvokedSignatureOfMatchedSignature(involvedClasses, selectedSignature);
		final FOPFeatureData[] featureData = (FOPFeatureData[]) selectedSignature.getFeatureData();
		for (int j = 0; j < featureData.length; j++) {
			final FOPFeatureData fopFeature = featureData[j];

			addToRefactoringSignatures(involvedClasses, selectedSignature, fopFeature.getFile());
		}

		System.out.println(involvedClasses);

		return involvedClasses;
	}

	private Set<RefactoringSignature> createRefactoringSignatures(final Set<AbstractClassSignature> involvedClasses2,
			final Set<AbstractSignature> matchedSignatures) {
		Set<RefactoringSignature> result = new HashSet<>();

		for (AbstractClassSignature involvedClass : involvedClasses2) {

			AbstractSignature matchedSignature = checkSignature(involvedClass, matchedSignatures);
			if (matchedSignature != null) {

				handleInvokedSignatureOfMatchedSignature(result, matchedSignature);

				final FOPFeatureData[] featureData = (FOPFeatureData[]) involvedClass.getFeatureData();
				for (int j = 0; j < featureData.length; j++) {
					final FOPFeatureData fopFeature = featureData[j];

					addToRefactoringSignatures(result, matchedSignature, fopFeature.getFile());
				}
			}
		}

		return result;
	}

	private void addToRefactoringSignatures(Set<RefactoringSignature> result, AbstractSignature matchedSignature, final IFile file) {
		RefactoringSignature signature = getRefactoringSignature(result, file);
		if (signature == null) {

			signature = new RefactoringSignature(file, matchedSignature);
			result.add(signature);
		} else if (signature.getDeclaration() == null) {
			signature.setDeclaration(matchedSignature);
		}
		signature.setRenameDeclaration(true);
	}

	private void handleInvokedSignatureOfMatchedSignature(Set<RefactoringSignature> result, AbstractSignature matchedSignature) {

		for (FOPFeatureData featureData : (FOPFeatureData[]) matchedSignature.getFeatureData()) {

			for (AbstractSignature invokedSignature : featureData.getInvokedSignatures()) {
				final FOPFeatureData[] invokedFeatureData = (FOPFeatureData[]) invokedSignature.getFeatureData();
				for (int i = 0; i < invokedFeatureData.length; i++) {
					final FOPFeatureData fopFeature = invokedFeatureData[i];
					final IFile file = fopFeature.getFile();

					RefactoringSignature signature = getRefactoringSignature(result, file);
					if (signature == null) {

						signature = new RefactoringSignature(file, matchedSignature);
						result.add(signature);
					}

					signature.addInvocation(invokedSignature);
				}
			}
		}
	}

	private Set<AbstractSignature> getSignaturesForFile(final Map<IFile, Set<AbstractSignature>> qwer, final IFile file) {
		final Set<AbstractSignature> signatures;
		if (qwer.containsKey(file)) {
			signatures = qwer.get(file);
		} else {
			signatures = new HashSet<>();
			qwer.put(file, signatures);
		}

		return signatures;
	}

	private Set<AbstractSignature> getMatchedSignatures() {
		Set<AbstractSignature> matched = new HashSet<>();
		final SignatureIterator iter = signatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();
			if (checkSignature(signature)) {
				matched.add(signature);
			}
		}

		return matched;
	}

	private void addSubAndSuperClasses(final Map<IFile, Set<AbstractSignature>> map, final AbstractClassSignature classSignature) {
		if (classSignature == null)
			return;

		addAbstractClassesForNames(map, classSignature.getImplementList());
		addAbstractClassesForNames(map, classSignature.getExtendList());
		addAbstractClassesForNames(map, classSignature.getSubClassesList());
	}

	private void addAbstractClassesForNames(final Map<IFile, Set<AbstractSignature>> map, final Set<String> names) {
		for (String className : names) {
			if (!classes.containsKey(className))
				continue;

			final AbstractClassSignature classSignature = classes.get(className);
			if (classSignature == null)
				return;

			final FOPFeatureData[] featureData = (FOPFeatureData[]) classSignature.getFeatureData();
			for (int j = 0; j < featureData.length; j++) {
				final FOPFeatureData fopFeature = featureData[j];

				final Set<AbstractSignature> signatures = getSignaturesForFile(map, fopFeature.getFile());
				if (!signatures.contains(classSignature)) {
					signatures.add(classSignature);
					addSubAndSuperClasses(map, classSignature);
				}
			}
		}
	}

	private void addSubAndSuperClasses(final Set<AbstractClassSignature> result, final AbstractClassSignature classSignature) {
		if (classSignature == null)
			return;

		addAbstractClassesForNames(result, classSignature.getImplementList());
		addAbstractClassesForNames(result, classSignature.getExtendList());
		addAbstractClassesForNames(result, classSignature.getSubClassesList());
	}

	private void addAbstractClassesForNames(final Set<AbstractClassSignature> result, final Set<String> names) {
		for (String className : names) {
			if (!classes.containsKey(className))
				continue;

			final AbstractClassSignature classSignature = classes.get(className);
			if (classSignature == null)
				return;

			if (!result.contains(classSignature)) {
				result.add(classSignature);
				addSubAndSuperClasses(result, classSignature);
			}
		}
	}

	private RefactoringSignature getRefactoringSignature(final Set<RefactoringSignature> result, final IFile file) {
		for (RefactoringSignature refactoringSignature : result) {
			if (refactoringSignature.getFile().equals(file))
				return refactoringSignature;
		}
		return null;
	}

	private AbstractSignature checkSignature(final AbstractClassSignature signature, Set<AbstractSignature> matchedSignatures) {
		for (AbstractSignature match : matchedSignatures) {
			if (match.getParent().equals(signature)) {
				return match;
			}
		}
		return null;
	}

	private Map<String, AbstractClassSignature> getClasses() {
		final Map<String, AbstractClassSignature> classes = new HashMap<>();

		final SignatureIterator iter = signatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();
			if (signature instanceof AbstractClassSignature)
				classes.put(signature.getName(), (AbstractClassSignature) signature);
		}

		return classes;
	}

	private void search(final RefactoringSignature refactoringSignatures) {

		final IFile file = refactoringSignatures.getFile();
		if ((file == null) || ((file != null) && !file.isAccessible()))
			return;

		ICompilationUnit unit = JavaCore.createCompilationUnitFrom(file);
		if (unit == null)
			return;

		IASTVisitor visitor = getASTVisitor(unit, refactoringSignatures);
		visitor.startVisit();

		nodes.put(unit, visitor.getMatches());
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

	private void rewriteAST(ICompilationUnit unit, List<SearchMatch> matches) {

		MultiTextEdit multiEdit = new MultiTextEdit();
		for (SearchMatch match : matches) {
			multiEdit.addChild(new ReplaceEdit(match.getOffset(), match.getLength(), newName));
		}

		if (!multiEdit.hasChildren())
			return;

		TextFileChange change = new TextFileChange(unit.getElementName(), (IFile) unit.getResource());
		change.setTextType("java");
		change.setEdit(multiEdit);

		changes.put(unit, change);
	}

}
