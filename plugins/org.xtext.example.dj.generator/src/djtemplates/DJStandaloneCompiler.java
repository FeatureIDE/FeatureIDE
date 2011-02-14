package djtemplates;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.List;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.mwe.utils.DirectoryCleaner;
import org.eclipse.emf.mwe.utils.StandaloneSetup;
import org.eclipse.xpand2.XpandExecutionContextImpl;
import org.eclipse.xpand2.XpandFacade;
import org.eclipse.xpand2.output.Outlet;
import org.eclipse.xpand2.output.OutputImpl;
import org.eclipse.xtend.typesystem.emf.EmfMetaModel;
import org.eclipse.xtext.resource.IResourceServiceProvider;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;
import org.xtext.example.DJStandaloneSetup;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Program;
import org.xtext.example.util.JavaProva;

import com.google.inject.Injector;

/**
 * This class compile a set of dj files.
 * @author Meglio Denis
 */
public class DJStandaloneCompiler {
	private String[] fileNames;
	private int errors = 0;
	private String errorReport = "";
	
	/**
	 * Creates a new compiler.
	 * @param fileNames the files to compile.
	 */
	public DJStandaloneCompiler(String[] fileNames) {
		this.fileNames = fileNames;
	}
	
	/**
	 * Creates a new compiler.
	 * @param fileName the file to compile.
	 */
	public DJStandaloneCompiler(String fileName) {
		this.fileNames = new String[]{fileName};
	}
	
	/**
	 * Returns the collected error messages.
	 * @return the error report.
	 */
	public String getErrorReport() {
		return errorReport;
	}
	
	/**
	 * Compile the files writing it in the 'src-gen' folder.
	 * The working path is the current working directory.
	 * @return <code>true</code> if the compiler compiled without errors, <code>false</code>
	 * otherwise.
	 */
	public boolean compile() {
		return compile("./src", "./src-gen/", "");
	}
	
	/**
	 * Compile the files writing it in the 'src-gen' folder.
	 * @param workingPath the path in which are located files.
	 * @return <code>true</code> if the compiler compiled without errors, <code>false</code>
	 * otherwise.
	 */
	public boolean compile(String inputWorkingPath, String outputWorkingPath, String uriPrefix) {
		errors = 0;
		errorReport = "";
		boolean ioError = false;
		
		for(String fileName : fileNames) {
		
				System.out.println("Compiling " + fileName);
				compileResource(fileName, inputWorkingPath, outputWorkingPath, uriPrefix);
		
				
		}
		
		System.out.println("Files compiled with " + errors + (errors == 1 ? " error" : " errors"));
		if(errors != 0) errorReport += "\n" + errors + " compile errors";
		
		return (errors == 0 && !ioError);
	}
		
	private void compileResource(String fileName, String inputWorkingPath, String outputWorkingPath, String uriPrefix) {

		/*Environment configuration*/

		StandaloneSetup standalone = new StandaloneSetup();
		
		standalone.setPlatformUri(inputWorkingPath);
		Injector injector = new DJStandaloneSetup().createInjectorAndDoEMFRegistration();
		XtextResourceSet resourceSet = injector.getInstance(XtextResourceSet.class);
		resourceSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);
		
		/*File parsing*/
		
		Resource resource = resourceSet.createResource(URI.createURI(uriPrefix + fileName));
		
		InputStream in = null;
		try {
			in = new FileInputStream(inputWorkingPath + fileName);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
	
		try {
			resource.load(in, resourceSet.getLoadOptions());
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		if(resource.getContents().size() == 0) {
			System.out.println("The file is empty: no folder has been generated");
			return;
		}
		Program model = (Program)resource.getContents().get(0);
		
		/* File validation */
		
		IResourceServiceProvider serviceProvider = injector.getInstance(IResourceServiceProvider.class);
		IResourceValidator resourceValidator = serviceProvider.getResourceValidator();
		List<Issue> validate = resourceValidator.validate(resource, CheckMode.ALL, null);
		for (Issue issue : validate) {
			printError(issue, fileName);
		}
		
		/* Folders cleanup */
		
		try {
			List<String> imports = JavaProva.urisToPackages(model);
			imports.add(JavaProva.uriToPackage(fileName));
			
			for(String imp : imports) {
				if(new java.io.File(outputWorkingPath + JavaProva.uriToPackage(model)).exists()) {
					System.out.println("Now cleaning " + outputWorkingPath + imp);
					DirectoryCleaner cleaner = new DirectoryCleaner();
					cleaner.cleanFolder(outputWorkingPath + imp);
					System.out.println("Cleaning has been succesfully done");
				}
			}
		} catch (FileNotFoundException ex) {
			ex.printStackTrace();
		}
				
		/*Code generation*/
		
		OutputImpl output = new OutputImpl();
		output.addOutlet(new Outlet(false, "UTF-8", null, true, outputWorkingPath));
		XpandExecutionContextImpl execCtx = new XpandExecutionContextImpl(output, null);
		execCtx.registerMetaModel(new EmfMetaModel(DJPackage.eINSTANCE));
		XpandFacade facade = XpandFacade.create(execCtx);
		facade.evaluate("djtemplates::Start::main", model);
	}
	
	private void printError(Issue issue, String fileName) {
		System.out.println((issue.isSyntaxError() ? "SYNTAX " : "") + "ERROR");
		System.out.println("\tFILE: " + fileName);
		System.out.println("\tLINE: " + issue.getLineNumber());
		System.out.println("\tDESCRIPTION: " + issue.getMessage());
		System.out.println("\tTARGET: " + issue.getUriToProblem());
		errors++;
	}
	
	public static void main(String[] args) throws IOException {
		if(args.length == 0)
			System.out.println("Insert at least one file to compile");
		else
			new DJStandaloneCompiler(args).compile();
	}  
	
	@SuppressWarnings("unused")
	private String inputStreamToString(InputStream in) throws IOException {
	    BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(in));
	    StringBuilder stringBuilder = new StringBuilder();
	    String line = null;

	    while ((line = bufferedReader.readLine()) != null) {
	    stringBuilder.append(line + "\n");
	    }

	    bufferedReader.close();
	    return stringBuilder.toString();
	    }
}