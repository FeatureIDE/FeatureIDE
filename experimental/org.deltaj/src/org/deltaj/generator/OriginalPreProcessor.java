/**
 * 
 */
package org.deltaj.generator;

import java.util.List;
import java.util.regex.Matcher;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.JavaVerbatim;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.StatementBlock;
import org.deltaj.deltaj.Original;
import org.eclipse.xtext.EcoreUtil2;

/**
 * Preprocess modification of methods and the original occurrences
 * 
 * @author bettini
 * 
 */
public class OriginalPreProcessor {

	public boolean preprocess(Method original, Method modified) {

		DeltaModule container = EcoreUtil2.getContainerOfType(modified, DeltaModule.class);
		if (container != null)
			return preprocess(original, modified, container.getName());
		else
			return false;
	}

	public boolean preprocess(Method original, Method modified, String deltaName) {

		String originalName = original.getName();
		String modifiedName = originalName + "$" + deltaName;
		original.setName(modifiedName);
		return preprocess(modified.getBody(), modifiedName);
	}

	protected boolean preprocess(StatementBlock body, String replacement) {

		if (body == null)
			return false;

		boolean originalReferenced = false;
		originalReferenced |= preprocessJavaVerbatim(body, replacement);
		originalReferenced |= preprocessOriginalInvocation(body, replacement);
		return originalReferenced;
	}

	protected boolean preprocessJavaVerbatim(StatementBlock body, String replacement) {

		boolean originalReferenced = false;
		List<JavaVerbatim> verbatims = EcoreUtil2.getAllContentsOfType(body, JavaVerbatim.class);
		for (JavaVerbatim javaVerbatim: verbatims) {
			String newVerbatim = replaceOriginalOccurrences(javaVerbatim.getVerbatim(), replacement);

			if (!newVerbatim.equals(javaVerbatim.getVerbatim())) {
				javaVerbatim.setVerbatim(newVerbatim);
				originalReferenced = true;
			}
		}
		return originalReferenced;
	}

	protected boolean preprocessOriginalInvocation(StatementBlock body, String replacement) {

		boolean originalReferenced = false;
		List<Original> originals = EcoreUtil2.getAllContentsOfType(body, Original.class);
		for (Original original: originals) {
			original.setMethod(replacement);
			originalReferenced = true;
		}
		return originalReferenced;
	}

	public String replaceOriginalOccurrences(String text, String replacement) {

		return text.replaceAll("original(?=\\s*\\()", Matcher.quoteReplacement(replacement));
	}

}
