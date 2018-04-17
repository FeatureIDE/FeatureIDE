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
package de.ovgu.featureide.munge.signatures;

import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.BodyDeclaration;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.Javadoc;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FeatureDataConstructor;
import de.ovgu.featureide.core.signature.base.PreprocessorFeatureData;

/**
 * Collects all signatures in a Munge project.
 *
 * @author Sebastian Krieter
 */
public abstract class MungeSignatureBuilder {

	private static String readFile(IFile file) throws CoreException {
		final int bufferSize = 1024;
		final char[] buffer = new char[bufferSize];
		final StringBuilder contents = new StringBuilder();

		try (final InputStreamReader in = new InputStreamReader(file.getContents())) {
			while (true) {
				final int readChars = in.read(buffer, 0, buffer.length);
				if (readChars < 0) {
					break;
				}
				contents.append(buffer, 0, readChars);
			}
		} catch (final IOException e) {
			CorePlugin.getDefault().logError(e);
		}
		return contents.toString();
	}

	private static Collection<AbstractSignature> parse(ProjectSignatures projectSignatures, ASTNode root) {
		final HashMap<AbstractSignature, AbstractSignature> map = new HashMap<>();

		final CompilationUnit cu = (CompilationUnit) root;
		final PackageDeclaration pckgDecl = cu.getPackage();
		final String packageName = (pckgDecl == null) ? null : pckgDecl.getName().getFullyQualifiedName();
		final List<?> l = cu.getCommentList();
		final List<Javadoc> cl = new LinkedList<>();
		for (final Object object : l) {
			if (object instanceof Javadoc) {
				final Javadoc comment = (Javadoc) object;
				cl.add(comment);
			}
		}

		final ListIterator<Javadoc> it = cl.listIterator();
		final FeatureDataConstructor featureDataConstructor = new FeatureDataConstructor(projectSignatures, FeatureDataConstructor.TYPE_PP);

		root.accept(new ASTVisitor() {

			private BodyDeclaration curDeclaration = null;
			private PreprocessorFeatureData curfeatureData = null;
			private String lastComment = null;
			private MethodDeclaration lastCommentedMethod = null;

			@Override
			public boolean visit(Javadoc node) {
				if (curDeclaration != null) {
					final StringBuilder sb = new StringBuilder();
					while (it.hasNext()) {
						final Javadoc comment = it.next();
						if (comment.getStartPosition() <= curDeclaration.getStartPosition()) {
							sb.append(comment);
							sb.append("\n");
						} else {
							it.previous();
							break;
						}
					}
					lastComment = sb.toString();

					curfeatureData.setComment(lastComment);
					lastCommentedMethod = (curDeclaration instanceof MethodDeclaration) ? (MethodDeclaration) curDeclaration : null;
				}
				return false;
			}

			private void attachFeatureData(AbstractSignature curSignature, BodyDeclaration curDeclaration) {
				this.curDeclaration = curDeclaration;
				final Javadoc javadoc = curDeclaration.getJavadoc();
				final int startPosition = (javadoc == null) ? curDeclaration.getStartPosition() : curDeclaration.getStartPosition() + javadoc.getLength();
				curfeatureData = (PreprocessorFeatureData) featureDataConstructor.create(null, unit.getLineNumber(startPosition),
						unit.getLineNumber(curDeclaration.getStartPosition() + curDeclaration.getLength()));
				curSignature.setFeatureData(curfeatureData);
				map.put(curSignature, curSignature);
			}

			@Override
			public boolean visit(CompilationUnit unit) {
				this.unit = unit;
				return true;
			}

			CompilationUnit unit = null;

			@Override
			public boolean visit(MethodDeclaration node) {
				final int pos = unit.getLineNumber(node.getBody().getStartPosition());
				final int end = unit.getLineNumber(node.getBody().getStartPosition() + node.getBody().getLength());
				final MungeMethodSignature methodSignature = new MungeMethodSignature(getParent(node.getParent()), node.getName().getIdentifier(),
						node.getModifiers(), node.getReturnType2(), node.parameters(), node.isConstructor(), pos, end);

				attachFeatureData(methodSignature, node);

				if ((node.getJavadoc() == null) && (lastCommentedMethod != null) && lastCommentedMethod.getName().equals(node.getName())) {
					curfeatureData.setComment(lastComment);
				} else {
					lastCommentedMethod = null;
				}
				return true;
			}

			private AbstractClassSignature getParent(ASTNode astnode) {
				final AbstractClassSignature sig;
				if (astnode instanceof TypeDeclaration) {
					final TypeDeclaration node = (TypeDeclaration) astnode;
					sig = new MungeClassSignature(null, node.getName().getIdentifier(), node.getModifiers(), node.isInterface() ? "interface" : "class",
							packageName);
				} else {
					return null;
				}
				final AbstractClassSignature uniqueSig = (AbstractClassSignature) map.get(sig);
				if (uniqueSig == null) {
					visit((TypeDeclaration) astnode);
				}
				return uniqueSig;
			}

			@Override
			public boolean visit(FieldDeclaration node) {
				for (final Iterator<?> it = node.fragments().iterator(); it.hasNext();) {
					final VariableDeclarationFragment fragment = (VariableDeclarationFragment) it.next();

					final MungeFieldSignature fieldSignature =
						new MungeFieldSignature(getParent(node.getParent()), fragment.getName().getIdentifier(), node.getModifiers(), node.getType());

					attachFeatureData(fieldSignature, node);
				}

				return true;
			}

			@Override
			public boolean visit(TypeDeclaration node) {
				final MungeClassSignature classSignature = new MungeClassSignature(getParent(node.getParent()), node.getName().getIdentifier(),
						node.getModifiers(), node.isInterface() ? "interface" : "class", packageName);

				attachFeatureData(classSignature, node);

				return super.visit(node);
			}

		});
		return map.keySet();
	}

	public static ProjectSignatures build(IFeatureProject featureProject) {
		final ProjectSignatures projectSignatures = new ProjectSignatures(featureProject.getFeatureModel());
		final ArrayList<AbstractSignature> signatureList = new ArrayList<>();

		@SuppressWarnings("deprecation")
		final ASTParser parser = ASTParser.newParser(AST.JLS4);

		final IFolder sourceFolder = featureProject.getSourceFolder();
		try {
			sourceFolder.accept(new IResourceVisitor() {

				@Override
				public boolean visit(IResource resource) throws CoreException {
					if (resource instanceof IFolder) {
						return true;
					} else if (resource instanceof IFile) {
						final char[] content = readFile((IFile) resource).toCharArray();
						if (content.length > 0) {
							parser.setSource(content);
							signatureList.addAll(parse(projectSignatures, parser.createAST(null)));
						}
					}

					return false;
				}
			});
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

		projectSignatures.setSignatureArray(signatureList.toArray(new AbstractSignature[0]));
		return projectSignatures;
	}
}
