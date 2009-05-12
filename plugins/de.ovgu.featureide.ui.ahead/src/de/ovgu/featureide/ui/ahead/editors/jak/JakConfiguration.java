/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.ahead.editors.jak;

import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jdt.ui.text.IColorManager;
import org.eclipse.jdt.ui.text.IJavaColorConstants;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.BufferedRuleBasedScanner;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

/**
 * 
 * @author Marcus Leich
 *
 */
public class JakConfiguration extends SourceViewerConfiguration {
	
	class SingleTokenScanner extends BufferedRuleBasedScanner {
        public SingleTokenScanner(TextAttribute attribute) {
            setDefaultReturnToken(new Token(attribute));
        }        
    }

	public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer) {
		PresentationReconciler reconciler = new PresentationReconciler();

		IColorManager cm = JavaUI.getColorManager();
		
		DefaultDamagerRepairer dr =	new DefaultDamagerRepairer(new JakCodeScanner());
		reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
		reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
		
		dr = new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(cm.getColor(IJavaColorConstants.JAVA_SINGLE_LINE_COMMENT))));
		reconciler.setDamager(dr, JakPartitionScanner.JAK_COMMENT);
		reconciler.setRepairer(dr, JakPartitionScanner.JAK_COMMENT);

		dr = new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(cm.getColor(IJavaColorConstants.JAVADOC_DEFAULT))));
		reconciler.setDamager(dr, JakPartitionScanner.JAK_JAVADOC);
		reconciler.setRepairer(dr, JakPartitionScanner.JAK_JAVADOC);
		
		return reconciler;
	}

}
