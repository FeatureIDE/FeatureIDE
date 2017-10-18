package br.ufal.ic.colligens.models;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.util.Log;

/**
 * @author Thiago Emmanuel
 *
 */
public class FileProxy {

	private String path;
	// temporary path defined by the user.
	private String newFilepath = null;
	private final IResource iResource;
	private final List<Log> logs;

	public FileProxy(IResource iResource) {
		this.iResource = iResource;

		path = getFullPath().substring(0, getFullPath().length() - getFileName().length());
		// Windows
		if (System.getProperty("file.separator").equals("\\")) {
			path = path.replace("/", "\\");
		}

		if (!Colligens.getDefault().getPreferenceStore().getBoolean("USE_INCLUDES")) {
			try {
				// Create temporary file.
				generate();
			} catch (final IOException e) {
				e.printStackTrace();
			}
		}

		logs = new LinkedList<Log>();

		deleteMarkers();
	}

	public String getFileName() {
		return iResource.getName();
	}

	public String getPath() {
		return path;
	}

	public String getFullPath() {
		return iResource.getFullPath().toOSString();
	}

	public String getFileReal() {
		return iResource.getLocation().toString();
	}

	public IResource getResource() {
		return iResource;
	}

	public List<Log> getLogs() {
		return logs;
	}

	/**
	 * @return full path of the file to analysis
	 */
	public String getFileToAnalyse() {
		if (newFilepath != null) {
			return newFilepath;
		}

		if (Colligens.getDefault().getPreferenceStore().getBoolean("USE_INCLUDES")) {
			return getFileReal();
		}

		return Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "projects" + path + getFileName();
	}

	public String getNoIncludeFile() throws IOException {
		if (newFilepath != null) {
			return newFilepath;
		}
		newFilepath = Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "projects" + path + getFileName();
		generate();
		return newFilepath;
	}

	public void setFileToAnalyse(String path) {
		newFilepath = path;
	}

	/**
	 * @throws IOException
	 */
	private void generate() throws IOException {

		final File filePath = new File(Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "projects" + getPath());

		filePath.mkdirs();

		final File temp = new File(Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "projects"
			+ System.getProperty("file.separator") + "temp.c");
		temp.createNewFile();

		final FileWriter fstreamout = new FileWriter(Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "projects"
			+ System.getProperty("file.separator") + "temp.c");
		final BufferedWriter out = new BufferedWriter(fstreamout);

		final FileInputStream fstream = new FileInputStream(getFileReal());
		// Get the object of DataInputStream
		final DataInputStream in = new DataInputStream(fstream);
		final BufferedReader br = new BufferedReader(new InputStreamReader(in));
		String strLine;
		// Read File Line By Line
		while ((strLine = br.readLine()) != null) {

			if ((strLine.contains("include") && strLine.contains("#") && strLine.startsWith("#"))) {
				out.write("//" + strLine + "\n");
			} else {
				out.write(strLine + "\n");
			}

		}

		in.close();
		out.close();

		final File tempFile =
			new File(Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "projects" + path + getFileName());

		tempFile.deleteOnExit();

		if (tempFile.exists()) {
			tempFile.delete();

		}
		temp.renameTo(tempFile);

		deleteMarkers();

	}

	public void deleteMarkers() {
		// remove markers
		try {
			getResource().deleteMarkers(Log.MARKER_TYPE, false, IResource.DEPTH_ZERO);
		} catch (final CoreException e) {
			// nothing
		}
	}
}
