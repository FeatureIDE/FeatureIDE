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

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;

import org.apache.commons.cli.ParseException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.search.SearchMatch;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;

import AST.Access;
import AST.BodyDecl;
import AST.ClassDecl;
import AST.CompilationUnit;
import AST.ImportDecl;
import AST.InterfaceDecl;
import AST.List;
import AST.MemberClassDecl;
import AST.MemberInterfaceDecl;
import AST.MethodDecl;
import AST.ParameterDeclaration;
import AST.Program;
import AST.ReferenceType;
import AST.TypeDecl;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
//import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob.ExtendedSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import fuji.CompilerWarningException;
import fuji.Composition;
import fuji.FeatureDirNotFoundException;
import fuji.Main;
import fuji.SemanticErrorException;
import fuji.SyntacticErrorException;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public class RenameMethodRefactoring extends RenameRefactoring<IMethod> {
	
	// Tabelle der Aenderungen pro CompilationUnit
	private Map<ICompilationUnit, TextFileChange> fChanges = null;
	
	public RenameMethodRefactoring(IMethod selection, IFeatureProject featureProject) {
		super(selection, featureProject);
	}

	@Override
	public String getName() {
		return "RenameMethod";
	}

	@Override
	public RefactoringStatus checkFinalConditions(final IProgressMonitor pm) throws CoreException, OperationCanceledException {
		final RefactoringStatus status = new RefactoringStatus();
		try {
			pm.beginTask("Checking preconditions...", 2);
			
			// 1. Erstelle eine Tabelle der Aenderungen pro .java-Datei (CompilationUnit)
			fChanges = new LinkedHashMap<ICompilationUnit, TextFileChange>();
			
			//compilationUnit=JavaCore.createCompilationUnitFrom(file);
			
			final Map<ICompilationUnit, Collection<SearchMatch>> units = new HashMap<ICompilationUnit, Collection<SearchMatch>>();
			units.put(renamingElement.getCompilationUnit(), new ArrayList());
			
			
			ExtendedFujiSignaturesJob efsj = new ExtendedFujiSignaturesJob(featureProject);
			efsj.addJobFinishedListener(new JobFinishListener() {
				@Override
				public void jobFinished(IJob finishedJob, boolean success) {
					signatures = featureProject.getFSTModel().getProjectSignatures();
				}
				
			});
			efsj.schedule();
			
//			ProjectSignatures signatures = featureProject.getFSTModel().getProjectSignatures();
//			if (signatures == null) return status;
//			
//			
//			final FSTModel model = featureProject.getFSTModel();
//			if (model != null) return status;
//			
//			SignatureIterator iter = signatures.iterator();
//			while (iter.hasNext())
//			{
//				AbstractSignature signature = iter.next();
//				if (signature.getName().equals(renamingElement.getElementName())) 
//				{
//					addElement(signature);
//					while (signature.getParent() != null) {
//						signature = signature.getParent();
//					}
//
//					final String fullName = signature.getFullName();
//					final String fileName = (fullName.startsWith(".")) ? fullName.substring(1) : fullName.replace('.', '/');
//
//					final int featureID = signature.getFeatureData()[0].getID();
//					final IFile iFile = model.getFeature(signatures.getFeatureName(featureID)).getRole(fileName + ".java").getFile();
//
//					if (!iFile.isAccessible()) return status;
//					
//					ICompilationUnit unit = JavaCore.createCompilationUnitFrom(iFile);
					
//					if (unit == null) return status;
//				}
//								
//							remaningElement.getDeclaringType().getElementName().equals(modifierString) &&
//							remaningElement.getReturnType().equals(type.value)*/)
//						{
//			}
			
			// 2. Erstelle eine Suchanfrage fuer eine Projektweite Suche nach allen Referenzen der Methode
//			Program ast = getFujiAst();
//			qqq(ast);
			
			
		} finally {
			//pm.done();
		}
		return status;

	}
	
	

//	/**
//	 * @param signature
//	 */
//	private void addElement(AbstractSignature signature) {
//		
//		JavaCore.createCompilationUnitFrom(signature.getParent()
//				ICompilationUnit unit = ((IMember) element).getCompilationUnit();
//				if (unit != null) {
//					Collection<SearchMatch> collection = units.get(unit);
//					if (collection  == null) {
//						collection = new ArrayList<SearchMatch>();
//						units.put(unit, collection);
//					}
//					collection.add(match);
//				}
//			}
//		}
//		
//	}

	private Program getFujiAst() 
	{
		final String sourcePath = featureProject.getSourcePath();
		final String[] fujiOptions = new String[] { "-" + Main.OptionName.CLASSPATH, FeatureHouseComposer.getClassPaths(featureProject),
				"-" + Main.OptionName.PROG_MODE, "-" + Main.OptionName.COMPOSTION_STRATEGY, Main.OptionName.COMPOSTION_STRATEGY_ARG_FAMILY, "-typechecker",
				"-" + Main.OptionName.BASEDIR, sourcePath };
		
		Program ast = null;
		final FeatureModel fm = featureProject.getFeatureModel();
		fm.getAnalyser().setDependencies();

		try {
			Main fuji = new Main(fujiOptions, fm, featureProject.getFeatureModel().getConcreteFeatureNames());
			Composition composition = fuji.getComposition(fuji);
			ast = composition.composeAST();
		} catch (IllegalArgumentException e) {
			e.printStackTrace();
		} catch (ParseException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (FeatureDirNotFoundException e) {
			e.printStackTrace();
		} catch (SyntacticErrorException e) {
			e.printStackTrace();
		} catch (SemanticErrorException e) {
			e.printStackTrace();
		} catch (CompilerWarningException e) {
			e.printStackTrace();
		} catch (UnsupportedModelException e) {
			e.printStackTrace();
		}
		return ast;
	}

	@Override
	public Change createChange(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		
		// TODO Auto-generated method stub
		return new CompositeChange(getName());
	}
	
	
		
//		ASTParser parser = ASTParser.newParser(AST.JLS3); 
//		parser.setKind(ASTParser.K_COMPILATION_UNIT);
//		parser.setSource(unit); // set source
//		parser.setResolveBindings(true); // we need bindings later on
//		return (CompilationUnit) parser.createAST(null /* IProgressMonitor */); // parse
//		
//		ASTRewrite rewriter = ASTRewrite.create(ast);
//		 
//		//for getting insertion position
//		TypeDeclaration typeDecl = (TypeDeclaration) astRoot.types().get(0);
//		MethodDeclaration methodDecl = typeDecl.getMethods()[0];
//		Block block = methodDecl.getBody();
//	 
//		ListRewrite listRewrite = rewriter.getListRewrite(block, Block.STATEMENTS_PROPERTY);
//		Statement placeHolder = (Statement) rewriter.createStringPlaceholder("//mycomment", ASTNode.EMPTY_STATEMENT);
//		listRewrite.insertFirst(placeHolder, null);
//	 
//		TextEdit edits = rewriter.rewriteAST();
//	 
//		// apply the text edits to the compilation unit
//		Document document = new Document(unit.getSource());
//	 
//		edits.apply(document);
//	 
//		// this is the code for adding statements
//		unit.getBuffer().setContents(document.get());

}

