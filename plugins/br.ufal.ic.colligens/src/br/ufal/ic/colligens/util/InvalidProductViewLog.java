package br.ufal.ic.colligens.util;

import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_PRODUCT_VARIANT;

import java.io.File;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import br.ufal.ic.colligens.activator.Colligens;

public class InvalidProductViewLog {

	public static final String MARKER_TYPE = Colligens.PLUGIN_ID + ".invalidproduct";

	private String productName;
	private String relativePath;

	public InvalidProductViewLog(String path) {
		final String pattern = Pattern.quote(System.getProperty("file.separator"));
		final String[] relativePath = path.split(pattern);
		this.relativePath = relativePath[relativePath.length - 3] + File.separator + relativePath[relativePath.length - 2] + File.separator
			+ relativePath[relativePath.length - 1];
		productName = relativePath[relativePath.length - 1];

		try {
			final IMarker marker = getFolder().createMarker(MARKER_TYPE);
			marker.setAttribute(IMarker.MESSAGE, INVALID_PRODUCT_VARIANT);
			marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
			marker.setAttribute(IMarker.LOCATION, this.relativePath);
		} catch (final CoreException e) {
			e.printStackTrace();
		}
	}

	public IFolder getFolder() {
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final IPath location = Path.fromOSString(relativePath);
		return workspace.getRoot().getFolder(location);
	}

	public String getProductName() {
		return productName;
	}

	public void setProductName(String productName) {
		this.productName = productName;
	}

	public String getRelativePath() {
		return relativePath;
	}

	public void setRelativePath(String relativePath) {
		this.relativePath = relativePath;
	}

}
