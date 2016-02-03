package de.ovgu.featureide.featuremake;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileReader;

public class FeatureMakeComposer extends ComposerExtensionClass {

	@Override
	public boolean hasFeatureFolder() {
		return false;		
	}
	
	@Override
	public boolean hasSourceFolder() {
		return false;
	}
	
	@Override
	public boolean createFolderForFeatures() {
		return false;
	}
	
	@Override
	public void performFullBuild(IFile config) {


		IFeatureModel model = CorePlugin.getFeatureProject(config)
				.getFeatureModel();
		Configuration cfg = new Configuration(model);
		final FileReader<Configuration> reader = new FileReader<>(Paths.get(config.getLocationURI()), cfg, ConfigurationManager.getFormat(config.getName()));
		reader.read();
		
		List<String> args = new ArrayList<String>();
		args.add("make");
		args.add("-B");
		StringBuilder sb = new StringBuilder();
		sb.append("USERDEFS=");
		for (SelectableFeature sbf : cfg.getFeatures()) {
			IFeature feature = sbf.getFeature();
			IFeatureStructure structure = feature.getStructure();
			
			if (sbf.getSelection() == Selection.SELECTED && structure.isConcrete()) {
				sb.append("-D").append(sbf.getName()).append(" ");
			}
		}
		String sourceDirectory = Paths.get(this.featureProject.getProject().getLocationURI()) + "/source/";
		args.add(sb.toString());
		args.add("-C"+sourceDirectory);
		args.add("-fMakefile");
		ProcessBuilder processBuilder = new ProcessBuilder(args);
		processBuilder.redirectErrorStream(true);
		try {
			final Process process = processBuilder.start();
			new Thread() {
		        @Override
				public void run() {
		            BufferedReader input = new BufferedReader(new InputStreamReader(process.getInputStream()));
		            String line = null;
		            MessageConsole console = findConsole("Console");
		            MessageConsoleStream out = console.newMessageStream();
		            
		            try {
		                while ((line = input.readLine()) != null) {
		                	out.println(line);
		                }
		            } catch (IOException e) {
		                e.printStackTrace();
		            }
		        }
		    }.start();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private MessageConsole findConsole(String name){
		ConsolePlugin plugin = ConsolePlugin.getDefault();
		IConsoleManager conMan = plugin.getConsoleManager();
		IConsole[] existing = conMan.getConsoles();
		for (int i = 0; i < existing.length; i++)
			if (name.equals(existing[i].getName()))
				return (MessageConsole) existing[i];
		
		//no console found, so create a new one
		MessageConsole myConsole = new MessageConsole(name, null);
		conMan.addConsoles(new IConsole[]{myConsole});
		return myConsole;
	}
	
	@Override
	public Mechanism getGenerationMechanism() {
		return IComposerExtensionClass.Mechanism.PREPROCESSOR;
	}

}
