package br.ufal.ic.colligens.models;

import static de.ovgu.featureide.fm.core.localization.StringTable.ANALYZING_SELECTED_FILES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NOT_A_VALID_FILE_FOUND_C;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.TYPECHEF_DID_NOT_RUN_CORRECTLY_;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.RandomAccessFile;
import java.net.URL;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.cdt.core.model.CModelException;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.ICProject;
import org.eclipse.cdt.core.model.IIncludeReference;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.internal.util.BundleUtility;
import org.prop4j.Node;
import org.prop4j.NodeWriter;

import br.ufal.ic.colligens.activator.Colligens;
import de.fosd.typechef.TypeChefFrontend;
import de.fosd.typechef.options.FrontendOptions;
import de.fosd.typechef.options.FrontendOptionsWithConfigFiles;
import de.fosd.typechef.options.OptionException;
import de.fosd.typechef.options.Options;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

@SuppressWarnings(RESTRICTION)
public class TypeChef {

	private IProject project;
	private boolean isFinish = false;
	private List<FileProxy> fileProxies;

	private final AbstractHeader header;
	private IProgressMonitor monitor = null;

	public TypeChef() {
		header = AbstractHeader.getInstance();
	}

	/**
	 *
	 */
	private void prepareFeatureModel() {
		final File inputFile = new File(project.getLocation().toOSString() + System.getProperty("file.separator") + "model.xml");
		final File outputFile = new File(Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "cnf.fm");
		BufferedWriter print = null;
		try {
			print = new BufferedWriter(new FileWriter(outputFile));

			final IFeatureModel fm = FeatureModelManager.load(inputFile.toPath()).getObject();

			final Node nodes = AdvancedNodeCreator.createCNF(fm);
			final StringBuilder cnf = new StringBuilder();
			cnf.append(nodes.toString(NodeWriter.javaSymbols));
			print.write(cnf.toString());
		} catch (final FileNotFoundException e) {
			Colligens.getDefault().logError(e);
		} catch (final IOException e) {
			Colligens.getDefault().logError(e);
		} finally {
			if (print != null) {
				try {
					print.close();
				} catch (final IOException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
		}
	}

	/**
	 * @param fileProxy
	 * @throws OptionException
	 */
	private FrontendOptions getOptions(FileProxy fileProxy) throws OptionException {

		final ArrayList<String> paramters = new ArrayList<String>();

		// paramters.add("--parserstatistics");

		paramters.add("-w");
		paramters.add("--lexNoStdout");
		paramters.add("--lexOutput");
		paramters.add(Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "lexOutput.c");

		if (Colligens.getDefault().getPreferenceStore().getBoolean("FEATURE_MODEL")) {
			prepareFeatureModel(); // General processing options String
			paramters.add("--featureModelFExpr");
			paramters.add(Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "cnf.fm");
		}

		final String typeChefPreference = Colligens.getDefault().getPreferenceStore().getString("TypeChefPreference");

		paramters.add(typeChefPreference);

		if (Colligens.getDefault().getPreferenceStore().getBoolean("USE_INCLUDES")) {
			// Project C includes
			final ICProject project = CoreModel.getDefault().getCModel().getCProject(AbstractHeader.getFile(fileProxy.getFileReal()).getProject().getName());

			try {
				final IIncludeReference includes[] = project.getIncludeReferences();
				for (int i = 0; i < includes.length; i++) {
					paramters.add("-I");
					paramters.add(includes[i].getElementName());
				}
			} catch (final CModelException e) {

				e.printStackTrace();
			}

		}

		final Collection<String> headersPath = header.getIncludes();

		for (final Iterator<String> iterator = headersPath.iterator(); iterator.hasNext();) {
			paramters.add("-h");
			paramters.add(iterator.next());
		}

		paramters.add(fileProxy.getFileToAnalyse());

		// this static variable was changed, private to public, the jar typechef.
		Options.maxOptionId = 0;

		final FrontendOptionsWithConfigFiles frontendOptions = new FrontendOptionsWithConfigFiles();

		final String[] paramterArray = paramters.toArray(new String[paramters.size()]);

		frontendOptions.parseOptions(paramterArray);

		frontendOptions.setPrintToStdOutput(false);

		return frontendOptions;

	}

	/**
	 * @return
	 */
	public boolean isFinish() {
		return isFinish;
	}

	/**
	 * @param resourceList
	 * @throws TypeChefException
	 */
	public void run(List<IResource> resourceList) throws TypeChefException {
		isFinish = false;

		fileProxies = resourceToFileProxy(resourceList);

		try {
			if (fileProxies.isEmpty()) {
				monitor = null;
				throw new TypeChefException(NOT_A_VALID_FILE_FOUND_C);
			}

			header.setProject(fileProxies.get(0).getResource().getProject().getName());

			header.setMonitor(monitor);

			header.run();

			monitorbeginTask(ANALYZING_SELECTED_FILES, fileProxies.size());

			for (final FileProxy fileProxy : fileProxies) {
				// Monitor Update
				monitorWorked(1);
				monitorSubTask(fileProxy.getFullPath());
				// end Monitor
				if (monitorIsCanceled()) {
					isFinish = true;
					break;
				}

				try {

					final TypeChefFrontend typeChefFrontend = new TypeChefFrontend();

					typeChefFrontend.processFile(getOptions(fileProxy), fileProxy);

					isFinish = true;
				} catch (final OptionException e) {
					e.printStackTrace();
					// If the analysis is not performed correctly,
					// and the analysis made ​​from the command line
					startCommandLineMode(fileProxy);

					isFinish = true;
				} catch (final Exception e) {
					e.printStackTrace();
					// If the analysis is not performed correctly,
					// and the analysis made ​​from the command line
					startCommandLineMode(fileProxy);

					isFinish = true;
				}

			}
		} catch (final PlatformException e1) {
			monitor = null;
			e1.printStackTrace();
			Colligens.getDefault().logError(e1);
		}
		monitor = null;
	}

	/**
	 * @param list
	 * @return
	 */
	private List<FileProxy> resourceToFileProxy(List<IResource> list) {
		final List<FileProxy> fileProxies = new LinkedList<FileProxy>();
		// pega um dos arquivos para descobrir qual projeto esta sendo
		// verificado...
		if ((project == null) && !list.isEmpty()) {
			project = list.get(0).getProject();
			// System.err.println(project.toString());
		}
		for (final IResource resouce : list) {
			final FileProxy fileProxy = new FileProxy(resouce);
			fileProxies.add(fileProxy);
		}

		return fileProxies;
	}

	/**
	 * @return
	 */
	public List<FileProxy> getFilesLog() {
		final List<FileProxy> list = new LinkedList<FileProxy>();

		for (final FileProxy fileProxy : fileProxies) {
			if (!fileProxy.getLogs().isEmpty()) {
				list.add(fileProxy);
			}
		}
		return list;
		// return xmlParser.getLogs();
	}

	/**
	 * @param fileProxy
	 * @throws TypeChefException
	 */
	private void startCommandLineMode(FileProxy fileProxy) throws TypeChefException {
		final XMLParserTypeChef xmlParser = new XMLParserTypeChef();

		final ArrayList<String> args = new ArrayList<String>();
		args.add(fileProxy.getFileToAnalyse());

		final String typeChefPreference = Colligens.getDefault().getPreferenceStore().getString("TypeChefPreference");

		URL url = BundleUtility.find(Colligens.getDefault().getBundle(), "lib/" + "TypeChef-0.3.5.jar");
		try {
			url = FileLocator.toFileURL(url);
		} catch (final IOException e) {
			Colligens.getDefault().logError(e);
		}
		final Path pathToTypeChef = new Path(url.getFile());

		if (Colligens.getDefault().getPreferenceStore().getBoolean("FEATURE_MODEL")) {
			prepareFeatureModel(); // General processing options String
			args.add(0, Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "cnf.fm");
			args.add(0, "--featureModelFExpr");
		}

		if (Colligens.getDefault().getPreferenceStore().getBoolean("USE_INCLUDES")) {
			// // Project C includes
			final ICProject project = CoreModel.getDefault().getCModel().getCProject(AbstractHeader.getFile(fileProxy.getFileReal()).getProject().getName());

			try {
				final IIncludeReference includes[] = project.getIncludeReferences();
				for (int i = 0; i < includes.length; i++) {
					args.add(0, includes[i].getElementName());
					args.add(0, "-I");
				}
			} catch (final CModelException e) {

				e.printStackTrace();
			}

		}

		final Collection<String> headersPath = header.getIncludes();

		for (final Iterator<String> iterator = headersPath.iterator(); iterator.hasNext();) {

			args.add(0, iterator.next());
			args.add(0, "-h");
		}

		args.add(0, typeChefPreference);

		// saved in the' temp directory
		final String outputFilePath = Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "output";

		try {
			RandomAccessFile arq = new RandomAccessFile(outputFilePath, "rw");
			arq.close();
			arq = new RandomAccessFile(outputFilePath + ".xml", "rw");
			arq.close();
		} catch (final Exception e) {
			e.printStackTrace();
		}

		args.add(0, "--errorXML=" + outputFilePath + ".xml");

		args.add(0, Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "lexOutput.c");
		args.add(0, "--lexOutput");
		args.add(0, "--lexNoStdout");
		args.add(0, "-w");
		args.add(0, pathToTypeChef.toOSString());
		args.add(0, "-jar");
		args.add(0, "java");

		for (final String s : args) {
			System.err.print(s + " ");
		}

		final ProcessBuilder processBuilder = new ProcessBuilder(args);

		BufferedReader input = null;
		BufferedReader error = null;
		try {
			final Process process = processBuilder.start();
			input = new BufferedReader(new InputStreamReader(process.getInputStream(), Charset.availableCharsets().get("UTF-8")));
			error = new BufferedReader(new InputStreamReader(process.getErrorStream(), Charset.availableCharsets().get("UTF-8")));
			boolean x = true;
			while (x) {
				try {
					String line;
					while ((line = input.readLine()) != null) {
						System.out.println(line);
						Colligens.getDefault().logWarning(line);
					}
					try {
						process.waitFor();
					} catch (final InterruptedException e) {
						System.out.println(e.toString());
						Colligens.getDefault().logError(e);
					}
					final int exitValue = process.exitValue();
					if (exitValue != 0) {
						throw new TypeChefException(TYPECHEF_DID_NOT_RUN_CORRECTLY_);
					}
					x = false;
				} catch (final IllegalThreadStateException e) {
					System.out.println(e.toString());
					Colligens.getDefault().logError(e);
				}
			}
		} catch (final IOException e) {
			System.out.println(e.toString());
			Colligens.getDefault().logError(e);
			throw new TypeChefException(TYPECHEF_DID_NOT_RUN_CORRECTLY_);
		} finally {
			try {
				if (input != null) {
					input.close();
				}
			} catch (final IOException e) {
				Colligens.getDefault().logError(e);
			} finally {
				if (error != null) {
					try {
						error.close();
					} catch (final IOException e) {
						Colligens.getDefault().logError(e);
					}
				}
			}
		}
		xmlParser.setFile(fileProxy);
		xmlParser.processFile();
	}

	public void setMonitor(IProgressMonitor monitor) {
		this.monitor = monitor;
	}

	private boolean monitorIsCanceled() {
		return monitor != null ? monitor.isCanceled() : false;
	}

	private void monitorWorked(int value) {
		if (monitor == null) {
			return;
		}
		monitor.worked(value);
	}

	private void monitorSubTask(String label) {
		if (monitor == null) {
			return;
		}
		monitor.subTask(label);
	}

	private void monitorbeginTask(String label, int size) {
		if (monitor == null) {
			return;
		}
		monitor.beginTask(label, size);
	}
}
