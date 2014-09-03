package br.ufal.ic.colligens.models;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Pattern;

import org.eclipse.cdt.core.CCorePlugin;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.model.CModelException;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.IIncludeReference;
import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTypedefNameSpecifier;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.preference.IPreferenceStore;

import tree.Node;
import util.Type;
import util.TypeGeneratorVisitor;
import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.ProjectExplorerController;
import core.GeneralFrontend;
import core.presence.condition.PresenceConditionVisitor;
import de.fosd.typechef.options.OptionException;

@SuppressWarnings("restriction")
public class StubsHeader extends AbstractHeader {
	// It keeps the C types.
	private final HashSet<String> types = new HashSet<String>();

	// It keeps the macros defined.
	private final HashSet<String> macros = new HashSet<String>();

	// private final HashSet<String> listFilesCDT = new HashSet<String>();

	private Collection<String> includes = null;

	@Override
	public void run() throws PlatformException {
		File stubs = new File(this.getIncludePath());

		if (stubs.exists())
			return;

		new File(Colligens.getDefault().getConfigDir().getAbsolutePath()
				+ System.getProperty("file.separator") + "projects").mkdirs();

		this.stubsCDT();

	}

	@Override
	public String getIncludePath() {
		// return super.getProject().getProject().getLocation().toOSString()
		// + "/stubs.h";
		return Colligens.getDefault().getConfigDir().getAbsolutePath()
				+ System.getProperty("file.separator") + "projects"
				+ System.getProperty("file.separator")
				+ super.getProject().getProject().getName() + "_stubs.h";
	}

	@Override
	public Collection<String> getIncludes() {
		ArrayList<String> collection = new ArrayList<String>();

		collection.add(this.getIncludePath());

		IPreferenceStore store = Colligens.getDefault().getPreferenceStore();
		if (store.getBoolean("USE_INCLUDES")) {
			PlatformHeader platformHeader = new PlatformHeader();
			try {
				platformHeader.setProject(this.getProject().getProject()
						.getName());
				platformHeader.run();
				collection.add(platformHeader.getIncludePath());
			} catch (PlatformException e) {
				e.printStackTrace();
			}
		}

		return collection;
	}

	public void stubsCDT() throws PlatformException {
		Collection<String> files = filesAllProject();
		for (Iterator<String> iterator = files.iterator(); iterator.hasNext();) {
			this.generateTypes(iterator.next());
		}

		File fileTemp = writeTypesToPlatformHeader();
		fileTemp.renameTo(new File(this.getIncludePath()));

	}

	public void stubsToTypechef(String stub) throws PlatformException {
		// this.copyIncludes();

		// Active configurations

		// String stubs_temp = this.writeTypesToPlatformHeader();
		//
		// this.stubsToTypechef(stubs_temp);
		// this.listFilesCDT.clear();

		// List<String> listFiles = filesAllProject();
		//
		// addFiles(new File(ResourcesPlugin.getWorkspace().getRoot()
		// .getLocation().toString()
		// + System.getProperty("file.separator")
		// + super.getProject().getProject().getName()));

		// monitorbeginTask("Generating stubs", includes.size());
		//
		// for (Iterator<String> iterator = includes.iterator(); iterator
		// .hasNext();) {
		// String include = iterator.next();
		// monitorWorked(1);
		// monitorSubTask(include);
		//
		// if (monitorIsCanceled()) {
		// return platformTemp.getAbsolutePath();
		// }
		// try {
		// File file = null;
		// try {
		// file = this.activateConfigs(include);
		// this.generateTypes(file.getAbsolutePath());
		// } catch (PlatformException e) {
		// continue;
		// }
		//
		// try {
		// super.getProject()
		// .getProject()
		// .refreshLocal(IResource.DEPTH_INFINITE,
		// new NullProgressMonitor());
		// } catch (CoreException e) {
		// // TODO Auto-generated catch block
		// e.printStackTrace();
		// }
		//
		// file.deleteOnExit();
		// } catch (IOException e) {
		//
		// e.printStackTrace();
		// }
		// }
		// new File(super.getProject().getProject().getLocation().toOSString()
		// + System.getProperty("file.separator") + "temp.c")
		// .deleteOnExit();

		IFolder folder = super.getProject().getProject().getFolder("/includes");

		ProjectExplorerController explorerController = new ProjectExplorerController();

		explorerController.addResource(folder);

		List<IResource> list = explorerController.getList();

		IIncludeReference iIncludeReference[] = null;
		try {
			iIncludeReference = super.getProject().getIncludeReferences();
		} catch (CModelException e) {
			e.printStackTrace();
		}

		List<Type> typesAll = new ArrayList<Type>();

		PlatformHeader platformHeader = new PlatformHeader();

		platformHeader.setProject(super.getProject().getProject().getName());

		platformHeader.setMonitor(monitor);

		platformHeader.run();

		monitorbeginTask("Generating stubs (TypeChef)", list.size());

		for (Iterator<IResource> iterator = list.iterator(); iterator.hasNext();) {
			IResource iResource = iterator.next();
			// FileProxy fileProxy = new FileProxy(iResource);
			monitorWorked(1);
			monitorSubTask(iResource.getLocation().toString());

			if (monitorIsCanceled()) {
				return;
			}
			ArrayList<String> paramters = new ArrayList<String>();

			paramters.add("--lexNoStdout");
			paramters.add("--parse");
			paramters.add("-w");

			paramters.add("-h");
			paramters.add(stub);
			paramters.add("-h");
			paramters.add(platformHeader.getIncludePath());

			for (int i = 0; i < iIncludeReference.length; i++) {
				paramters.add("-I");
				paramters.add(iIncludeReference[i].getElementName());
			}

			paramters.add(iResource.getLocation().toString());

			try {
				Node myAst = GeneralFrontend.getAST(paramters);

				myAst.accept(new PresenceConditionVisitor());

				TypeGeneratorVisitor typeGenerator = new TypeGeneratorVisitor();
				myAst.accept(typeGenerator);

				// myAst.accept(new VisitorPrinter(false));
				//
				// myAst.toString();

				List<Type> types = typeGenerator.getTypes();
				for (Type type : types) {
					typesAll.add(type);
				}

			} catch (OptionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (NullPointerException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				throw new PlatformException("");
			}
		}
		System.err.println(typesAll.size());
		for (Type type : typesAll) {
			System.out.println(type.getPresenceCondition().toString());
			System.out.println(type.getSource());
		}
		System.err.println(typesAll.size());
		throw new PlatformException("Not a valid file C in ");

	}

	private void generateTypes(String filePath) throws PlatformException {

		try {
			// file = activateConfigs(filePath);
			// System.out.println(file.getAbsolutePath());
			ITranslationUnit tu = (ITranslationUnit) CoreModel.getDefault()
					.create(getFile(filePath));

			IASTTranslationUnit ast = null;

			IIndex index = CCorePlugin.getIndexManager().getIndex(
					super.getProject());
			// The AST is ready for use..
			ast = tu.getAST(index, ITranslationUnit.AST_PARSE_INACTIVE_CODE);

			this.setTypes(ast);
			this.setMacros(ast);
		} catch (CoreException e1) {

			throw new PlatformException(
					"Was not possible to generate the stubs");
			// } catch (IOException e) {
			// TODO Auto-generated catch block
			// e.printStackTrace();
			//
			// throw new PlatformException(
			// "Was not possible to generate the stubs");
		}
	}

	// It finds probable macros in the node.
	private void setMacros(IASTNode node) {
		IASTPreprocessorMacroDefinition[] definitions = node
				.getTranslationUnit().getMacroDefinitions();
		for (IASTPreprocessorMacroDefinition definition : definitions) {
			String macro = definition.getRawSignature();
			if (!this.macros.contains(macro)) {
				this.macros.add(macro);
			}

		}
	}

	// It finds probable types in the node.
	private void setTypes(IASTNode node) {
		IASTNode[] nodes = node.getChildren();
		if (node.getClass()
				.getCanonicalName()
				.equals("org.eclipse.cdt.internal.core.dom.parser.c.CASTTypedefNameSpecifier")) {

			CASTTypedefNameSpecifier s = (CASTTypedefNameSpecifier) node;
			String type = s.getRawSignature().replace("extern", "")
					.replace("static", "").replace("const", "").trim();
			String type2 = type;
			type = "typedef struct " + type + ";";
			if (!this.types.contains(type) && this.isValidJavaIdentifier(type2)) {
				this.types.add(type);
			}
		}

		for (int i = 0; i < nodes.length; i++) {
			this.setTypes(nodes[i]);
		}

	}

	// All types found are defined in the platform.h header file.
	private File writeTypesToPlatformHeader() throws PlatformException {

		File platformTemp = new File(super.getProject().getProject()
				.getLocation().toOSString()
				+ System.getProperty("file.separator") + "sutbs_temp.h");

		try {
			FileWriter writer = new FileWriter(platformTemp);
			for (Iterator<String> i = this.types.iterator(); i.hasNext();) {
				String type = i.next();
				if (!countDirectives.directives.contains(type)) {
					// writer.write("typedef struct {} " + type + ";\n");
					writer.write(type + "\n");
				}
			}

			for (Iterator<String> i = this.macros.iterator(); i.hasNext();) {
				String next = i.next();
				if (next.contains("#define ")) {
					String[] temp = next.trim().split(Pattern.quote(" "));
					if (!(countDirectives.directives.contains(temp[1])
							|| temp[1].endsWith("_H_") || temp[1]
								.endsWith("_H"))) {
						writer.write(next + "\n");
					}
				} else {
					writer.write(next + "\n");
				}
			}

			writer.flush();
			writer.close();
		} catch (IOException e) {
			throw new PlatformException(
					"was not possible to generate the stubs");
		}

		super.refreshLocal();

		return platformTemp;
	}

	private boolean isValidJavaIdentifier(String s) {
		// An empty or null string cannot be a valid identifier
		if (s == null || s.length() == 0) {
			return false;
		}

		char[] c = s.toCharArray();
		if (!Character.isJavaIdentifierStart(c[0])) {
			return false;
		}

		for (int i = 1; i < c.length; i++) {
			if (!Character.isJavaIdentifierPart(c[i])) {
				return false;
			}
		}

		return true;
	}

	// private void addFiles(File file) {
	// if (file.isFile()) {
	// if (file.getAbsolutePath().endsWith(".c")
	// || file.getAbsolutePath().endsWith(".h")) {
	// listFilesCDT.add(file.getAbsolutePath());
	// }
	// } else if (file.isDirectory()) {
	// for (File files : file.listFiles()) {
	// addFiles(files);
	// }
	//
	// }
	// }

	public void copyIncludes() throws PlatformException {
		if (monitorIsCanceled()) {
			return;
		}

		List<String> list;

		List<String> listFiles = filesAllProject();

		list = new ArrayList<String>(listFiles);

		try {
			IIncludeReference includes[] = super.getProject()
					.getIncludeReferences();
			for (int i = 0; i < includes.length; i++) {
				// System.out.println(includes[i].getElementName());
				list.add(0, "-I" + includes[i].getElementName());
			}
		} catch (CModelException e) {

			e.printStackTrace();
		}

		if (!Colligens.getDefault().getPreferenceStore().getString("LIBS")
				.contentEquals("")) {
			list.add(
					0,
					Colligens.getDefault().getPreferenceStore()
							.getString("LIBS"));
		}

		list.add(0, "-M");
		list.add(0, Colligens.getDefault().getPreferenceStore()
				.getString("GCC"));

		ProcessBuilder processBuilder = new ProcessBuilder(list);

		BufferedReader input = null;
		BufferedReader error = null;

		String output = new String();

		try {
			Process process = processBuilder.start();
			input = new BufferedReader(new InputStreamReader(
					process.getInputStream(), Charset.availableCharsets().get(
							"UTF-8")));
			error = new BufferedReader(new InputStreamReader(
					process.getErrorStream(), Charset.availableCharsets().get(
							"UTF-8")));
			boolean execute = true;

			while (execute) {

				try {
					String line;
					String errorLine = "";
					try {

						while ((line = input.readLine()) != null) {
							output = output.concat(line);
						}
						errorLine = "";
						while ((line = error.readLine()) != null) {
							if (line.contains("fatal error")) {
								errorLine = line;
								break;
							}
							System.err.println(line);
						}
					} catch (Exception e) {
						e.printStackTrace();
						Colligens.getDefault().logError(e);
					}

					try {
						process.waitFor();
					} catch (InterruptedException e) {
						System.out.println(e.toString());
						Colligens.getDefault().logError(e);
					}
					int exitValue = process.exitValue();
					if (exitValue != 0) {

						if (errorLine.equals("")) {
							errorLine = "Was not possible to locate all the includes (exit="
									+ exitValue + ")!";
						}
						throw new PlatformException(errorLine);
					}

					execute = false;
				} catch (IllegalThreadStateException e) {
					System.out.println(e.toString());
					Colligens.getDefault().logError(e);
				}
			}

		} catch (IOException e) {
			System.out.println(e.toString());
			Colligens.getDefault().logError(e);
		} finally {
			try {
				if (input != null) {
					input.close();
				}

			} catch (IOException e) {
				Colligens.getDefault().logError(e);
			} finally {
				if (error != null)
					try {
						error.close();
					} catch (IOException e) {
						Colligens.getDefault().logError(e);
					}
			}
		}

		Collection<String> listTemp = new HashSet<String>(Arrays.asList(output
				.split(" ")));

		Collection<String> includesTemp = new HashSet<String>();

		String projectPath = super.getProject().getProject().getLocation()
				.toOSString();

		for (Iterator<String> iterator = listTemp.iterator(); iterator
				.hasNext();) {
			String string = iterator.next();
			string = string.trim();
			if (!(string.contains("\\") || string.contains(".o:"))
					&& !includesTemp.contains(string)) {
				includesTemp.add(string);
			}
		}

		listTemp.clear();

		new File(projectPath + System.getProperty("file.separator")
				+ "includes").mkdirs();

		IIncludeReference includesPath[] = null;
		try {
			includesPath = super.getProject().getIncludeReferences();
		} catch (CModelException e) {
			e.printStackTrace();
		}

		includes = new HashSet<String>();

		for (Iterator<String> iterator = includesTemp.iterator(); iterator
				.hasNext();) {
			String string = iterator.next();

			for (int i = 0; i < includesPath.length; i++) {
				if (string.contains(includesPath[i].getElementName())) {
					System.err.println(string);
					String temp = string.substring(includesPath[i]
							.getElementName().length());

					File file = new File(projectPath + "/includes" + temp);

					if (file.exists()) {
						continue;
					}

					new File(projectPath
							+ "/includes"
							+ temp.substring(0, temp.length()
									- file.getName().length())).mkdir();

					includes.add(file.getAbsolutePath());
					try {
						FileWriter fstreamout = new FileWriter(
								file.getAbsolutePath());
						BufferedWriter out = new BufferedWriter(fstreamout);

						FileInputStream fstream;

						fstream = new FileInputStream(string);

						// Get the object of DataInputStream
						DataInputStream in = new DataInputStream(fstream);
						BufferedReader br = new BufferedReader(
								new InputStreamReader(in));
						String strLine;
						// Read File Line By Line
						while ((strLine = br.readLine()) != null) {

							if ((strLine.contains("include") && strLine
									.startsWith("#"))) {
								// out.write("//" + strLine + "\n");
							} else {
								out.write(strLine + "\n");
							}

						}

						in.close();
						out.close();
					} catch (FileNotFoundException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					break;
				}
			}
		}

		super.refreshLocal();

	}

	public File activateConfigs(String path) throws IOException,
			PlatformException {
		File file = new File(path);
		if (file.getName().endsWith(".c") || file.getName().endsWith(".h")) {

			File temp = new File(super.getProject().getProject().getLocation()
					.toOSString()
					+ System.getProperty("file.separator") + "temp.c");
			FileWriter fw = new FileWriter(temp);
			BufferedWriter bw = new BufferedWriter(fw);

			bw.write("#define COLLIGENS\n");

			FileInputStream fstream = new FileInputStream(
					file.getAbsoluteFile());
			DataInputStream in = new DataInputStream(fstream);
			BufferedReader br = new BufferedReader(new InputStreamReader(in));
			String strLine;
			while ((strLine = br.readLine()) != null) {
				strLine = strLine.trim();
				if (strLine.startsWith("#if") || strLine.startsWith("# if")
						|| strLine.startsWith("#  if")
						|| strLine.startsWith("#   if")) {
					bw.write("#ifdef COLLIGENS\n");
				} else if (strLine.startsWith("#el")
						|| strLine.startsWith("# el")
						|| strLine.startsWith("#  el")
						|| strLine.startsWith("#   el")) {
					bw.write("#endif\n");
					bw.write("#ifdef COLLIGENS\n");
				} else if (strLine.startsWith("#error")
						|| strLine.startsWith("# error")
						|| strLine.startsWith("#pragma")
						|| strLine.startsWith("# pragma")) {
					// bw.write("\\" + strLine + "\n");
				} else if ((strLine.contains("include") && strLine
						.startsWith("//#"))) {
					bw.write(strLine.substring(2, strLine.length()) + "\n");
				} else {
					bw.write(strLine + "\n");
				}

			}
			br.close();
			fstream.close();
			bw.close();

			super.refreshLocal();

			return temp;

		} else {

			throw new PlatformException("");
		}

	}

}
