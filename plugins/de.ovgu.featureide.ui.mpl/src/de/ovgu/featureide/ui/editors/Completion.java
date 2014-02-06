/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.editors;

import java.text.Collator;
import java.util.ArrayList;
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
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.jface.viewers.StyledString.Styler;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;

/**
 * Context Completion
 * 
 * @author Reimar Schröter
 */
@SuppressWarnings("restriction")
public class Completion implements IJavaCompletionProposalComputer {

	private Collator col = Collator.getInstance();

	public Completion() {
		col.setStrength(Collator.SECONDARY);
	}

	@Override
	public List<IContextInformation> computeContextInformation(
			ContentAssistInvocationContext arg0, IProgressMonitor arg1) {
		List<IContextInformation> list = new ArrayList<IContextInformation>();
		return list;
	}

	@Override
	public String getErrorMessage() {
		System.out.println();
		return null;
	}

	@Override
	public void sessionEnded() {
		System.out.println();

	}

	@Override
	public void sessionStarted() {
		System.out.println();

	}

//	private ProjectStructure projectStructure = null;

	@Override
	public List<ICompletionProposal> computeCompletionProposals(
			ContentAssistInvocationContext arg0, IProgressMonitor arg1) {

		final IFile file = ((IFileEditorInput) PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor().getEditorInput()).getFile();
		
		final InterfaceProject interfaceProject = MPLPlugin.getDefault().getInterfaceProject(file.getProject());
		final ArrayList<ICompletionProposal> list = new ArrayList<ICompletionProposal>();
		
		if (interfaceProject == null)
			return list;

		final IFeatureProject featureProject = interfaceProject.getFeatureProjectReference();
		
		if (featureProject == null)
			return list;
		
		String featureName = featureProject.getFeatureName(file);
		JavaContentAssistInvocationContext context = (JavaContentAssistInvocationContext) arg0;

		String prefix = new String(context.getCoreContext().getToken());

//		projectStructure = MPLPlugin.getDefault().extendedModules_getStruct(featureProject, featureName);
//		if (projectStructure == null) {
//			return list;
//		}
//		List<CompletionProposal> l = MPLPlugin.getDefault().extendedModules(projectStructure);
		List<CompletionProposal> l = MPLPlugin.getDefault().extendedModules_getCompl(interfaceProject, featureName);	

		for (CompletionProposal curProp : l) {
			curProp.setReplaceRange(context.getInvocationOffset()
					- context.getCoreContext().getToken().length,
					context.getInvocationOffset());

			if (curProp.getKind() == CompletionProposal.TYPE_REF) {
				LazyJavaCompletionProposal prsss = new LazyJavaCompletionProposal(
						curProp, context);

				prsss.setStyledDisplayString(new StyledString(new String(
						curProp.getCompletion())));
				prsss.setReplacementString(new String(curProp.getCompletion()));
				if (prefix.length() >= 0
						&& new String(curProp.getCompletion())
								.startsWith(prefix)) {
					list.add(prsss);
				}
			} else if (curProp.getKind() == CompletionProposal.METHOD_REF) {
				LazyJavaCompletionProposal meth = new LazyJavaCompletionProposal(
						curProp, context);

				String displayString = new String(curProp.getCompletion());
				displayString = displayString.concat("(");
				int paramNr = Signature.getParameterCount(curProp
						.getSignature());
				for (int i = 0; i < paramNr; i++) {
					displayString = displayString.concat(Signature
							.getParameterTypes(curProp.getSignature())
							+ " arg"
							+ i);
					if (i + 1 < paramNr) {
						displayString = displayString.concat(", ");
					}
				}
				displayString = displayString.concat(") : ");
				// displayString = displayString.concat(new
				// String(Signature.getReturnType(curProp.getSignature())));

				StyledString methString = new StyledString(displayString);
				Styler styler = StyledString.createColorRegistryStyler(
						JFacePreferences.DECORATIONS_COLOR,
						JFacePreferences.CONTENT_ASSIST_BACKGROUND_COLOR);
				// TextStyle style = new
				// TextStyle(JFaceResources.getDefaultFont(),JFaceResources.getResources().createColor(new
				// RGB(10, 10,
				// 10)),JFaceResources.getResources().createColor(new
				// RGB(0,0,0)));
				// styler.applyStyles(style);
				StyledString infoString = new StyledString(new String(" - "
						+ new String(curProp.getName()) + " " + featureName),
						styler);
				methString.append(infoString);
				meth.setStyledDisplayString(methString);

				meth.setReplacementString(new String(curProp.getCompletion()));

				if (prefix.length() >= 0
						&& new String(curProp.getCompletion())
								.startsWith(prefix)) {
					list.add(meth);
				}
			} else if (curProp.getKind() == CompletionProposal.FIELD_REF) {
				LazyJavaCompletionProposal field = new LazyJavaCompletionProposal(
						curProp, context);
				StyledString fieldString = new StyledString(new String(
						curProp.getCompletion()));
				Styler styler = StyledString.createColorRegistryStyler(
						JFacePreferences.DECORATIONS_COLOR,
						JFacePreferences.CONTENT_ASSIST_BACKGROUND_COLOR);
				StyledString infoString = new StyledString(new String(" - "
						+ new String(curProp.getName()) + " " + featureName),
						styler);
				fieldString.append(infoString);
				field.setStyledDisplayString(fieldString);

				field.setReplacementString(new String(curProp.getCompletion()));
				if (prefix.length() > 0
						&& new String(curProp.getCompletion())
								.startsWith(prefix)) {
					list.add(field);
				}
			}
		}
		return list;
	}

}
