package de.ovgu.featureide.featurec;

import java.io.ByteArrayInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;


public class FeatureCComposer extends ComposerExtensionClass {

	private FeatureHouseComposer composer;
	private static final String MAPPINGS_FILENAME = ".autotools_mappings";
	private static final Map<String,String> config_parameter = new HashMap<String,String>();
	
	
	public FeatureCComposer() {
		composer = new FeatureHouseComposer();
	}

	
	
	@Override
	public void performFullBuild(IFile config) {
		composer.initialize(CorePlugin.getDefault().getFeatureProject(config));
		composer.performFullBuild(config);
		
		FeatureModel model = CorePlugin.getDefault().getFeatureProject(config).getFeatureModel();
		Configuration cfg = new Configuration(model);
		ConfigurationReader cr = new ConfigurationReader(cfg);
		try {
			cr.readFromFile(config);
		} catch (CoreException | IOException e) {
			e.printStackTrace();
		}
		
		IResource mappings = config.getProject().findMember(MAPPINGS_FILENAME);
		if(mappings != null && mappings.isAccessible() && mappings instanceof IFile){
			try {
				List<String> content_lines = Files.readAllLines(Paths.get(mappings.getLocation().toOSString()));
				for(String line : content_lines){
					String[] key_value = line.split(";");
					if(key_value.length == 2){
						config_parameter.put(key_value[0], key_value[1]);
					}
					else{
						CorePlugin.getDefault().logError("Mappings file invalid", new IllegalArgumentException());
					}
					
				}
			} catch (IOException e) {
				e.printStackTrace();
			}			
		} 
		
		StringBuilder sb = new StringBuilder();
		for(SelectableFeature sbf : cfg.getFeatures()){
			if(sbf.getSelection() == Selection.SELECTED){
				sb.append(config_parameter.getOrDefault(sbf.getName(), "")).append(" ");
			}
		}
		IResource autotools_default = config.getProject().findMember(".autotools_default");
		if(autotools_default.isAccessible() && autotools_default instanceof IFile){
			try {
				String content = new String(Files.readAllBytes(Paths.get(autotools_default.getLocation().toOSString())));
				content = content.replace("@@",sb.toString());
				IFile auto_tools = (IFile)config.getProject().findMember(".autotools");
				if(auto_tools.isAccessible()){				      
					try(InputStream inputStream = new ByteArrayInputStream(content.getBytes("UTF-8"))){
						auto_tools.setContents(inputStream, true,true,new NullProgressMonitor());					
//						auto_tools.refreshLocal(IResource.DEPTH_INFINITE, null);
					} catch (CoreException e) {
						e.printStackTrace();
					}
					
					System.out.println(Files.readAllLines(Paths.get(auto_tools.getLocation().toOSString())));
				}
				
				
			} catch (IOException e) {
				e.printStackTrace();
			} 
		}
		
	}

	@Override
	public Mechanism getGenerationMechanism() {
		return composer.getGenerationMechanism();
	}

}
