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
package de.ovgu.featureide.ui.editors;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.CompletionProposal;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.internal.ui.text.java.LazyJavaCompletionProposal;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.preference.JFacePreferences;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.jface.viewers.StyledString.Styler;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * Context Completion
 *
 * @author Reimar Schr�ter
 */
@SuppressWarnings("restriction")
public class Completion implements IJavaCompletionProposalComputer {

	// private Collator col = Collator.getInstance();

	public Completion() {
		// col.setStrength(Collator.FULL_DECOMPOSITION);
	}

	@Override
	public List<IContextInformation> computeContextInformation(ContentAssistInvocationContext arg0, IProgressMonitor arg1) {
		return Collections.emptyList();
	}

	@Override
	public String getErrorMessage() {
		return null;
	}

	@Override
	public void sessionEnded() {

	}

	@Override
	public void sessionStarted() {}

	@Override
	public List<ICompletionProposal> computeCompletionProposals(ContentAssistInvocationContext arg0, IProgressMonitor arg1) {

		JavaContentAssistInvocationContext context = null;
		if (arg0 instanceof JavaContentAssistInvocationContext) {
			context = (JavaContentAssistInvocationContext) arg0;
		}

		final IFile file =
			((IFileEditorInput) PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor().getEditorInput()).getFile();
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(file);

		if ((context == null) || (featureProject == null) || (featureProject.getProjectSignatures() == null)) {
			return Collections.emptyList();
		}

		final String featureName = featureProject.getFeatureName(file);

		final ArrayList<ICompletionProposal> list = new ArrayList<ICompletionProposal>();
		String prefix = "";
		try {
			prefix = ((JavaContentAssistInvocationContext) arg0).computeIdentifierPrefix().toString();
		} catch (final BadLocationException e1) {
			e1.printStackTrace();
		}

		final List<CompletionProposal> completionProp = CorePlugin.getDefault().extendedModules_getCompl(featureProject, featureName);

		for (final CompletionProposal curProp : completionProp) {
			curProp.setReplaceRange(context.getInvocationOffset() - context.getCoreContext().getToken().length, context.getInvocationOffset());

			if (curProp.getKind() == CompletionProposal.TYPE_REF) {
				final LazyJavaCompletionProposal prsss = new LazyJavaCompletionProposal(curProp, context);

				prsss.setStyledDisplayString(new StyledString(new String(curProp.getCompletion())));
				prsss.setReplacementString(new String(curProp.getCompletion()));
				if ((prefix.length() >= 0) && new String(curProp.getCompletion()).startsWith(prefix)) {
					list.add(prsss);
				}
			} else if (curProp.getKind() == CompletionProposal.METHOD_REF) {
				final LazyJavaCompletionProposal meth = new LazyJavaCompletionProposal(curProp, context);

				String displayString = new String(curProp.getCompletion());
				displayString = displayString.concat("(");
				int paramNr = 0;
				try {
					paramNr = Signature.getParameterCount(curProp.getSignature());
				} catch (final IllegalArgumentException e) {
					e.printStackTrace();
				}

				for (int i = 0; i < paramNr; i++) {
					String paramName = new String(Signature.getParameterTypes(curProp.getSignature())[i]);
					paramName = normalize(paramName);
					displayString = displayString.concat(paramName + " arg" + i);
					if ((i + 1) < paramNr) {
						displayString = displayString.concat(", ");
					}
				}
				displayString = displayString.concat(") : ");

				displayString = displayString.concat(normalize(new String(Signature.getReturnType(curProp.getSignature()))));

				final StyledString methString = new StyledString(displayString);
				final Styler styler =
					StyledString.createColorRegistryStyler(JFacePreferences.DECORATIONS_COLOR, JFacePreferences.CONTENT_ASSIST_BACKGROUND_COLOR);
				// TextStyle style = new
				// TextStyle(JFaceResources.getDefaultFont(),JFaceResources.getResources().createColor(new
				// RGB(10, 10,
				// 10)),JFaceResources.getResources().createColor(new
				// RGB(0,0,0)));
				// styler.applyStyles(style);
				final StyledString infoString =
					new StyledString(new String(" - " + normalize(new String(curProp.getDeclarationSignature())) + " " + featureName), styler);
				methString.append(infoString);
				meth.setStyledDisplayString(methString);

				meth.setReplacementString(new String(curProp.getCompletion()));

				if ((prefix.length() >= 0) && new String(curProp.getCompletion()).startsWith(prefix)) {
					list.add(meth);
				}
			} else if (curProp.getKind() == CompletionProposal.FIELD_REF) {
				final LazyJavaCompletionProposal field = new LazyJavaCompletionProposal(curProp, context);
				final StyledString fieldString = new StyledString(new String(curProp.getCompletion()));
				final Styler styler =
					StyledString.createColorRegistryStyler(JFacePreferences.DECORATIONS_COLOR, JFacePreferences.CONTENT_ASSIST_BACKGROUND_COLOR);
				final StyledString infoString = new StyledString(new String(" - " + new String(curProp.getName()) + " " + featureName), styler);
				fieldString.append(infoString);
				field.setStyledDisplayString(fieldString);

				field.setReplacementString(new String(curProp.getCompletion()));
				if ((prefix.length() > 0) && new String(curProp.getCompletion()).startsWith(prefix)) {
					list.add(field);
				}
			}
		}
		return list;
	}

	private String normalize(String paramName) {
		int firstIDX = paramName.lastIndexOf('.');
		if (firstIDX <= 0) {
			firstIDX = 1;
		}
		paramName = paramName.substring(firstIDX, paramName.length() - 1);
		return paramName;
	}
}
