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
	private IResource iResource;
	private List<Log> logs;

	public FileProxy(IResource iResource) {
		this.iResource = iResource;

		path = getFullPath().substring(0,
				getFullPath().length() - getFileName().length());
		// Windows
		if (System.getProperty("file.separator").equals("\\")) {
			path = path.replace("/", "\\");
		}

		if (!Colligens.getDefault().getPreferenceStore()
				.getBoolean("GLOBAL_ANALYZE")) {
			try {
				generate();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		this.logs = new LinkedList<Log>();

		this.deleteMarkers();
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

	public IResource getFileIResource() {
		return iResource;
	}

	public List<Log> getLogs() {
		return logs;
	}

	/**
	 * @return full path of the file to analysis
	 */
	public String getFileToAnalyse() {
		if (Colligens.getDefault().getPreferenceStore()
				.getBoolean("GLOBAL_ANALYZE")) {
			return getFileReal();
		}
		return Colligens.getDefault().getConfigDir().getAbsolutePath()
				+ System.getProperty("file.separator") + "projects" + path
				+ getFileName();
	}

	/**
	 * @throws IOException
	 */
	private void generate() throws IOException {

		File filePath = new File(Colligens.getDefault().getConfigDir()
				.getAbsolutePath()
				+ System.getProperty("file.separator") + "projects" + getPath());

		filePath.mkdirs();

		File temp = new File(Colligens.getDefault().getConfigDir()
				.getAbsolutePath()
				+ System.getProperty("file.separator")
				+ "projects"
				+ System.getProperty("file.separator") + "temp.c");
		temp.createNewFile();

		FileWriter fstreamout = new FileWriter(Colligens.getDefault()
				.getConfigDir().getAbsolutePath()
				+ System.getProperty("file.separator")
				+ "projects"
				+ System.getProperty("file.separator") + "temp.c");
		BufferedWriter out = new BufferedWriter(fstreamout);

		FileInputStream fstream = new FileInputStream(getFileReal());
		// Get the object of DataInputStream
		DataInputStream in = new DataInputStream(fstream);
		BufferedReader br = new BufferedReader(new InputStreamReader(in));
		String strLine;
		// Read File Line By Line
		while ((strLine = br.readLine()) != null) {

			if ((strLine.contains("include") && strLine.contains("#") && strLine
					.startsWith("#"))) {
				out.write("//" + strLine + "\n");
			} else {
				out.write(strLine + "\n");
			}

		}

		in.close();
		out.close();

		File tempFile = new File(getFileToAnalyse());

		tempFile.deleteOnExit();

		if (tempFile.exists()) {
			tempFile.delete();

		}
		temp.renameTo(tempFile);

		this.deleteMarkers();

	}

	public void deleteMarkers() {
		// remove markers
		try {
			this.getFileIResource().deleteMarkers(Log.MARKER_TYPE, false,
					IResource.DEPTH_ZERO);
		} catch (CoreException e) {
			// e.printStackTrace();
		}
	}
}
