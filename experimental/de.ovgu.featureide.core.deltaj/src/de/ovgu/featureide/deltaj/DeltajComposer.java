/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.deltaj;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;

import org.deltaj.DeltaJStandaloneSetup;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.xtext.generator.IGenerator;
import org.eclipse.xtext.generator.JavaIoFileSystemAccess;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;

import com.google.inject.Injector;

import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;

/**
 * DeltaJ Composer
 * 
 * @author Fabian Benduhn
 * @author Sven Schuster
 */
public class DeltajComposer extends ComposerExtensionClass {
	private static final String PLUGIN_ID_XTEXT = "org.eclipse.xtext";
	private static final String PLUGIN_ID_XTYPES = "it.xtypes";
	private static final String PLUGIN_WARNING_XTEXT = "The required bundle "+PLUGIN_ID_XTEXT+" is not installed.";
	private static final String PLUGIN_WARNING_XTYPES = "The required bundle "+PLUGIN_ID_XTYPES+" is not installed.";

	public static final String COMPOSER_ID = "de.ovgu.featureide.composer.deltaj";
	public static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	public static final String FILE_EXT = ".deltaj";
	public static final String FILENAME_RULES = "rules.deltas";
	
	private String configName;
	private String outputPath;
	
	private DeltajSPLDefinition spl;
	private FeatureModel featureModel;

	private int errors = 0;
	private String errorReport = "";

	private IGenerator generator;
	private JavaIoFileSystemAccess fileAccess;
	private IResourceValidator validator;
	
	private List<Issue> issueList;
	private List<DeltajFile> deltajFiles;
	
	private MessageConsoleStream consoleMessageStream = null;
	
	@Override
	public void performFullBuild(IFile config) {
		if(!isPluginInstalled(PLUGIN_ID_XTEXT)){
			generateWarning(PLUGIN_WARNING_XTEXT);
			return;
		}
		if(!isPluginInstalled(PLUGIN_ID_XTYPES)){
			generateWarning(PLUGIN_WARNING_XTYPES);
			return;
		}
		// init console
		MessageConsole console = new MessageConsole("DeltaJ Error Log", null);
		console.activate();
		ConsolePlugin.getDefault().getConsoleManager().addConsoles(new IConsole[]{ (IConsole) console });
		consoleMessageStream = console.newMessageStream();
		
		// initialization
		this.errors = 0;
		this.errorReport = "";
		boolean ioError = false;
		this.outputPath = this.featureProject.getBuildPath().replace('\\', '/') + "/";
		this.configName = config.getName().split("\\.")[0];
		this.spl = new DeltajSPLDefinition();
		IFolder sourceFolder = featureProject.getSourceFolder();
		this.featureModel = featureProject.getFeatureModel();
		this.spl.setName(this.featureModel.getRoot().getName());
		
		// get all features
		this.spl.addAllFeatures(this.featureModel.getConcreteFeatures());
		
		// get deltas specification
		this.spl.setDeltas(parseApplicationRules());
		
		// get current configuration
		Configuration configuration = new Configuration(this.featureModel);
		ConfigurationReader reader = new ConfigurationReader(configuration);
		try {
			reader.readFromFile(config);
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}
		
		// collect all deltaj files of selected features
		String composedDeltas = "";
		deltajFiles = new ArrayList<DeltajFile>();
		composedDeltas += composeAllFileContents(sourceFolder);
		composedDeltas += this.spl.toString();
		composedDeltas += this.createProductDefinition(configuration);
		
		IFile tmpFile = featureProject.getProject().getFile(featureProject.getBuildFolder().getName() + "/tmp" + DeltajComposer.FILE_EXT);
		InputStream in = new ByteArrayInputStream(composedDeltas.getBytes());
		try {
			tmpFile.create(in, false, null);
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}
		
		// compile
		compileResource(tmpFile.getFullPath().toString());
		
		// cleanup
		try {
			tmpFile.delete(false, null);
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}
		
		// print errors
		
		if (!issueList.isEmpty()) {
			for (Issue issue : issueList) {
				printError(issue);
			}
		}
		consoleMessageStream.print("DeltaJ Files compiled with " + this.errors + (this.errors == 1 ? " error" : " errors"));
		if(this.errors != 0 || ioError) {
			this.errorReport += "\n" + this.errors + " compile errors";
			System.out.println(this.errorReport);
		}
	}
	
	private String parseApplicationRules() {
		String deltas = "";
		try {
			InputStream source = null;
			source = this.featureProject.getProject().getFile(DeltajComposer.FILENAME_RULES).getContents();
			BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(source));
			StringBuilder stringBuilder = new StringBuilder();
			String line = null;
			while ((line = bufferedReader.readLine()) != null)
				stringBuilder.append(line + "\n");
			bufferedReader.close();
			deltas += stringBuilder.toString() + "\n"; 
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}
		return deltas;
	}
	
	private String composeAllFileContents(IFolder folder) {
		String contents = "";
		try {
			int lineNumber = 0;
			for(IResource member : folder.members()) {
				if(member.getType() == IResource.FILE && DeltajComposer.FILE_EXT.equals("." + member.getFileExtension())) {
					DeltajFile file = new DeltajFile((IFile) member,lineNumber,0);
					
					InputStream source = null;
					source = ((IFile) member).getContents();
					BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(source));
					StringBuilder stringBuilder = new StringBuilder();
					String line = null;
					while ((line = bufferedReader.readLine()) != null) {
						stringBuilder.append(line + "\n");
						lineNumber++;
					}
					bufferedReader.close();
					contents += stringBuilder.toString() + "\n";
					file.setEndLine(lineNumber++);
					this.deltajFiles.add(file);
				}
				else if(member.getType() == IResource.FOLDER) {
					contents += composeAllFileContents((IFolder) member);
				}
			}
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}
		return contents;
	}
	
	private String createProductDefinition(Configuration configuration) {
		String ret = "product " + this.configName + " from " + this.featureModel.getRoot().getName() + " : {";
		int i = 0;
		for(Iterator<Feature> iter = configuration.getSelectedFeatures().iterator(); iter.hasNext();) {
			Feature feature = iter.next();
			if(!feature.isAbstract()) {
				if(i++ != 0)
					ret += ", ";
				ret += feature.getName();
			}
		}
		return ret + "}";
	}
	
	private void compileResource(String fileName) {
		// get instances
		Injector injector = new DeltaJStandaloneSetup().createInjectorAndDoEMFRegistration();
		ResourceSet set = injector.getInstance(ResourceSet.class);
		validator = injector.getInstance(IResourceValidator.class);
		fileAccess = injector.getInstance(JavaIoFileSystemAccess.class);
		generator = injector.getInstance(IGenerator.class);
		
		Resource resource = set.getResource(URI.createURI(getUriPrefix() + fileName), true);
		
		// validate the resource for syntax errors
		issueList = validator.validate(resource, CheckMode.ALL, CancelIndicator.NullImpl);
		
		// generate
		fileAccess.setOutputPath(this.outputPath);
		generator.doGenerate(resource, fileAccess);
	}

	@Override
	public LinkedHashSet<String> extensions() {
		LinkedHashSet<String> extensions = new LinkedHashSet<String>();
		extensions.add(FILE_EXT);
		return extensions;
	}

	private String getUriPrefix() {
		return "platform:/resource/";
	}
	
	private void printError(Issue issue) {
		DeltajFile file = getDeltajFileFromTmpLine(issue.getLineNumber());
		String s = "" + (issue.isSyntaxError() ? "SYNTAX " : "") + "ERROR" + "\n"
				+ (file != null ? "LINE:\t\t" + (issue.getLineNumber() - file.getStartLine()) + "\n" : "")
				+ (file != null ? "FILE:\t\t" + file.getMember().getFullPath() + "\n" : "")
				+ "DESCRIPTION:\t" + issue.getMessage() + "\n\n";
		consoleMessageStream.print(s);
		this.errors++;
	}
	
	private DeltajFile getDeltajFileFromTmpLine(int line) {
		for(DeltajFile file : deltajFiles) {
			if(line >= file.getStartLine() && line <= file.getEndLine()) {
				return file;
			}
		}
		return null;
	}
	
	@Override
	public boolean hasFeatureFolder() {
		return false;
	}
	

	@Override
	public boolean createFolderForFeatures() {
		return false;
	}

	@Override
	public boolean refines() {
		return false;
	}
	
	@Override
	public ArrayList<String[]> getTemplates() {
		return TEMPLATES;
	}
	
	private static final ArrayList<String[]> TEMPLATES = createTempltes();
	
	private static ArrayList<String[]> createTempltes() {
		 ArrayList<String[]> list = new  ArrayList<String[]>(8);
		 list.add(new String[]{"DeltaJ", "deltaj", "delta " + CLASS_NAME_PATTERN + " {\n\t\n}"});
		 return list;
	}

	@Override
	public Mechanism getGenerationMechanism() {
	    return IComposerExtensionClass.Mechanism.DELTA_ORIENTED_PROGRAMMING;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionBase#supportsMigration()
	 */
	@Override
	public boolean supportsMigration()
	{
		return false;
	}
}
