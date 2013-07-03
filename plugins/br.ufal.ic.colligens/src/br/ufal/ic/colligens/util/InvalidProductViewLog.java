package br.ufal.ic.colligens.util;

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
		String pattern = Pattern.quote(System.getProperty("file.separator"));
		String[] relativePath = path.split(pattern);
		this.relativePath = relativePath[relativePath.length - 3]
				+ File.separator + relativePath[relativePath.length - 2]
				+ File.separator + relativePath[relativePath.length - 1];
		this.productName = relativePath[relativePath.length - 1];

		try {
			IMarker marker = getFolder().createMarker(MARKER_TYPE);
			marker.setAttribute(IMarker.MESSAGE, "Invalid product variant");
			marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
			marker.setAttribute(IMarker.LOCATION, this.relativePath);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	public IFolder getFolder() {
		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IPath location = Path.fromOSString(this.relativePath);
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
