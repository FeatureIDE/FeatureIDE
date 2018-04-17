package de.ovgu.featureide.oscar.propertyusage.core;

import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.StringLiteral;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;

import de.ovgu.featureide.oscar.IO.Console;
import de.ovgu.featureide.oscar.IO.ExportImport;
import de.ovgu.featureide.oscar.model.Feature;
import oscar.OscarProperties;
import oscar.Startup;

/**
 * Our PropertyUsageHandler handler extends AbstractHandler, an IHandler base class.
 * 
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class PropertyUsage {

	private static final String JDT_NATURE = "org.eclipse.jdt.core.javanature";
	private Boolean DEBUG = false;
	
	private String outputmode;
	private IProject project;
	private IProject reportProject;
	private IFile properties; 
	
	//Create the Console to log the results
	private final Console console = new Console();

	// Load all key/value pairs from Oscar property file. Expects a copy of
	// oscar_mcmaster.properties in src/resources/. Commented out
	// properties in original are uncommented in this copy.
	private OscarProperties op ;

	// Get expected OscarProperty method names
	final private Set<String> oscarPropertyMethods;

	// Used to store OscarProperty method names found by visiting AST
	// nodes. Will compare with static method names in oscarPropertyMethods.
	// Used to detect modifications to the OscarProperties class.
	final private Set<String> oscarPropertyMethodsCheck = new HashSet<String>();

	// Store OscarProperties MethodInvocation nodes found during AST search
	final private Set<ASTNode> astNodes = new HashSet<ASTNode>();

	// Stores OscarProperties MethodDeclaration nodes found during AST search
	final private Set<ASTNode> astOscarPropertyNodes = new HashSet<ASTNode>();

	// Used to store {<key, [number of usages, number of boolean usages]>}.
	final private Map<String, Integer[]> allPropMap ;
	
	//Hierarchy model in FDL language
	private Feature base;
	

	private String varName = null;
	private Boolean isOscarPropertiesVariable = null;
	
	
	

	public PropertyUsage(boolean db, IProject pj, IFile pr, String om, IProject reportProj) {
		super();
		this.project = pj;
		this.properties=pr;
		this.outputmode=om;
		this.DEBUG=db;
		this.reportProject=reportProj;
		this.op=loadOscarProperties();
		this.oscarPropertyMethods = getOscarPropertiesMethods();
		this.allPropMap = initializePropertyMap();
	}

	public OscarProperties loadOscarProperties() {
		Startup start = new Startup(this.properties,this.project);
		start.contextInitialized();
		OscarProperties op = new OscarProperties(this.properties);	
		return op;
	}

	// Initialization adds all properties found in the Oscar properties
	// file. Needed to detect properties in the Oscar properties file
	// that are not actually used in the code base.
	public Map<String, Integer[]> initializePropertyMap() {
		Map<String, Integer[]> propMap = new HashMap<String, Integer[]>();
		Integer[] init_val = new Integer[] { 0, 0 };
		for (String key : op.stringPropertyNames()) {
			propMap.put(key, init_val);
		}
		console.writeln("Oscar Property map count:" + propMap.size());
		return propMap;
	}

	// Records count of properties found with provision for adding
	// properties not present in the Oscar properties file.
	public void addProperty(String key, Boolean b) {
		if (!allPropMap.containsKey(key)) {
			// not present in Oscar properties file
			// and first time encountered in the code base
			allPropMap.put(key, new Integer[] { 0, 0 });
		}
		Integer[] intArray = allPropMap.get(key);
		int totalCount = intArray[0] + 1;
		int boolCount;
		if (b) {
			boolCount = intArray[1] + 1;
		} else {
			boolCount = intArray[1];
		}
		allPropMap.put(key, new Integer[] { totalCount, boolCount });
	}

	public Set<String> getOscarPropertiesMethods() {
		String[] methods = { "getProperty", "getInstance", "readFromFile", "hasProperty", "getBooleanProperty",
				"isPropertyActive", "getStartTime", "isTorontoRFQ", "isProviderNoAuto", "isPINEncripted",
				"isSiteSecured", "isAdminOptionOn", "isLogAccessClient", "isLogAccessProgram",
				"isAccountLockingEnabled", "isOntarioBillingRegion", "isBritishColumbiaBillingRegion",
				"isAlbertaBillingRegion", "isCaisiLoaded", "getDbType", "getDbUserName", "getDbPassword", "getDbUri",
				"getDbDriver", "getBuildDate", "getBuildTag", "isOscarLearning", "faxEnabled", "isRxFaxEnabled",
				"isConsultationFaxEnabled", "isEFormSignatureEnabled", "isEFormFaxEnabled", "isFaxEnabled",
				"isRxSignatureEnabled", "isConsultationSignatureEnabled", "isSpireClientEnabled",
				"getSpireClientRunFrequency", "getSpireServerUser", "getSpireServerPassword", "getSpireServerHostname",
				"getSpireDownloadDir", "getHL7A04BuildDirectory", "getHL7A04SentDirectory", "getHL7A04FailDirectory",
				"getHL7SendingApplication", "getHL7SendingFacility", "getHL7ReceivingApplication",
				"getHL7ReceivingFacility", "isHL7A04GenerationEnabled", "isEmeraldHL7A04TransportTaskEnabled",
				"getEmeraldHL7A04TransportAddr", "getEmeraldHL7A04TransportPort", "getIntakeProgramAccessServiceId",
				"getIntakeProgramCashServiceId", "getIntakeProgramAccessFId", "getConfidentialityStatement",
				"getIntakeProgramCashFId", "isLdapAuthenticationEnabled" };
		Set<String> theSet = new HashSet<String>();
		Collections.addAll(theSet, methods);
		return theSet;
	}

	private Boolean compareOscarPropertiesMethods(Set<String> hardCodedSet, Set<String> discoveredSet) {
		Boolean result = true;
		for (String s : hardCodedSet) {
			// the 'getProperty' method is inherited from Properties so not
			// specified in OscarProperties
			if (!s.equals("getProperty") && !discoveredSet.contains(s)) {
				console.writeln("Property not found in discovered set: " + s);
				return false;
			}
		}
		for (String s : discoveredSet) {
			if (!s.equals("OscarProperties") && !hardCodedSet.contains(s)) {
				console.writeln("Property not found in hardcoded set: " + s);
				return false;
			}
		}
		return result;
	}

	public void reportResults() {
		console.writeln("Method count: " + oscarPropertyMethods.size() );
		console.writeln("Method nodes found: " + astOscarPropertyNodes.size());
		if (DEBUG) {
			console.writeln("Discovered OscarProperties Methods:");
			for (String methodName : oscarPropertyMethods) {
				console.writeln(methodName);
			}
		}
		if (!compareOscarPropertiesMethods(oscarPropertyMethods, oscarPropertyMethodsCheck)) {
			console.writeln("Hard-coded OscarProperties methods no longer match methods discovered in OscarProperies.java");
		} else {
			console.writeln("No new OscarProperties methods found");
		}
		
		this.base=HierarchyReconstruction.getFDLHierarchy(op,allPropMap,1);

		ExportImport.export(this.base,op,allPropMap,outputmode,reportProject);
		

		console.writeln("Nodes found: " + astNodes.size());
		console.writeln("Number properties expected: " + op.size());
		console.writeln("Number properties found: " + allPropMap.size());
	}


	public void findProject() {

		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IWorkspaceRoot root = workspace.getRoot();
		console.writeln("root " + root.getLocation().toOSString());
		try {
			if (project.isOpen() && project.isNatureEnabled(JDT_NATURE)) {
				console.writeln("Project [" + project.getName() + "] has Java nature");
				analyseMethods(project);
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	private void analyseMethods(IProject project) throws JavaModelException {
		
		IPackageFragment[] packages = JavaCore.create(project).getPackageFragments();
		// parse(JavaCore.create(project));
		DateFormat dateFormat = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
		Date date = new Date();
		console.writeln(dateFormat.format(date)); // 2016/11/16 12:08:43
		for (IPackageFragment mypackage : packages) {
			if (mypackage.getKind() == IPackageFragmentRoot.K_SOURCE) {
				createAST(mypackage);
			}
		}
		reportResults();
		console.writeln(dateFormat.format(new Date()));


	}

	private void createAST(IPackageFragment mypackage) throws JavaModelException {
		

		for (ICompilationUnit unit : mypackage.getCompilationUnits()) {

			CompilationUnit cu = parse(unit);

			cu.accept(new ASTVisitor() {

				// Search oscar.OscarProperties for methods
				@Override
				public boolean visit(MethodDeclaration node) {
					// store names of all the oscar.OscarProperty methods to
					// detect additions/deletions
					if (cu.getPackage().getName().toString().equals("oscar")
							&& cu.getJavaElement().getElementName().equals("OscarProperties.java")) {
						Collections.addAll(oscarPropertyMethodsCheck, node.getName().toString());
						Boolean r = astOscarPropertyNodes.add(node);
						if (!r) {
							console.writeln("Unxpected presence of node " + node.getName().toString());
						}
					}
					return true;
				}

				public boolean visit(MethodInvocation node) {
					IMethodBinding binding = node.resolveMethodBinding();
					if (binding != null) {
						ITypeBinding type = binding.getDeclaringClass();
						if (type != null && type.getName().toString().equals("OscarProperties")) {
							if (!node.arguments().isEmpty() && node.arguments().get(0) instanceof StringLiteral) {
								StringLiteral stringLiteral = (StringLiteral) node.arguments().get(0);
								Boolean r = astNodes.add(node);
								if (!r) {
									console.writeln("Unexpected presence of node " + node.getName().toString());
								}
								Boolean b = isBoolean((StringLiteral) node.arguments().get(0));
								if (DEBUG)
									printDebugInfo(cu, node, type, stringLiteral, b);
								addProperty(stringLiteral.getLiteralValue(), b);
							}
						} else if (node.getName().toString().equals("get")
								&& (node.toString().startsWith("OscarProperties.getInstance().get(")
										|| node.toString().startsWith("oscar.OscarProperties.getInstance().get("))) {
							// finds oddities like
							// (String)OscarProperties.getInstance().get("myoscar_server_base_url")
							if (!node.arguments().isEmpty() && node.arguments().get(0) instanceof StringLiteral) {
								StringLiteral stringLiteral = (StringLiteral) node.arguments().get(0);
								Boolean r = astNodes.add(node);
								if (!r) {
									console.writeln("Unexpected presence of node " + node.getName().toString());
								}
								Boolean b = isBoolean(stringLiteral);
								if (DEBUG)
									printDebugInfo(cu, node, type, stringLiteral, b);
								addProperty(stringLiteral.getLiteralValue(), b);
							}
						} else if (type != null && type.getName().toString().equals("OscarPropertiesCheck")) {
							if (!node.arguments().isEmpty() && node.arguments().get(0) instanceof StringLiteral) {
								StringLiteral stringLiteral = (StringLiteral) node.arguments().get(0);
								String key = ((StringLiteral) node.arguments().get(0)).getLiteralValue();
								if (!(node.toString().contains(".setValue(\"" + key + "\")")
										|| node.toString().contains(".setDefaultVal(\"" + key + "\")")
										|| node.toString().contains(".setReverse(\"" + key + "\")"))) {
									Boolean r = astNodes.add(node);
									if (!r) {
										console.writeln("Unexpected presence of node " + node.getName().toString());
									}
									Boolean b = true;
									if (DEBUG)
										printDebugInfo(cu, node, type, stringLiteral, b);
									addProperty(key, b);
								}
							}
						} else if (type != null && type.getName().toString().equals("IsPropertiesOn")) {
							if (!node.arguments().isEmpty() && node.arguments().get(0) instanceof StringLiteral) {
								StringLiteral stringLiteral = ((StringLiteral) node.arguments().get(0));
								Boolean r = astNodes.add(node);
								if (!r) {
									console.writeln("Unexpected presence of node " + node.getName().toString());
								}
								Boolean b = true;
								if (DEBUG)
									printDebugInfo(cu, node, type, stringLiteral, b);
								addProperty(stringLiteral.getLiteralValue(), b);
							}
						} else if (type != null && type.getName().toString().equals("IsModuleLoadTag")) {
							if (!node.arguments().isEmpty() && node.arguments().get(0) instanceof StringLiteral) {
								StringLiteral stringLiteral = (StringLiteral) node.arguments().get(0);
								String key = stringLiteral.getLiteralValue();
								if (node.toString().contains(".setModuleName(\"" + key + "\")")) {
									Boolean r = astNodes.add(node);
									if (!r) {
										console.writeln("Unexpected presence of node " + node.getName().toString());
									}
									Boolean b = true;
									if (DEBUG)
										printDebugInfo(cu, node, type, stringLiteral, b);
									addProperty(key, b);
								}
							}
						} else if (type != null && type.getName().toString().equals("Properties")) {
							//if (node.getName().toString().equals("load")) console.writeln(getPackageAndFilename(cu));
							if (!node.arguments().isEmpty() && node.arguments().get(0) instanceof StringLiteral) {
								StringLiteral stringLiteral = (StringLiteral) node.arguments().get(0);
								String key = stringLiteral.getLiteralValue();
								if (cu.getPackage().getName().toString().equals("oscar")
										&& cu.getJavaElement().getElementName().equals("OscarProperties.java")) {
									Boolean r = astNodes.add(node);
									if (!r) {
										console.writeln("Unexpected presence of node " + node.getName().toString());
									}
									Boolean b = isBoolean((StringLiteral) node.arguments().get(0));
									if (DEBUG)
										printDebugInfo(cu, node, type, stringLiteral, b, false);
									addProperty(key, b);
								} else {
									String[] tmp = node.toString().split("\\.getProperty\\(");
									if (tmp.length > 1) {
										varName = tmp[0];
										isOscarPropertiesVariable = false;
										if (!varName.contains(",")
												&& varName.contains("OscarProperties.getInstance()")) {
											isOscarPropertiesVariable = true;
										} else {
											cu.accept(new ASTVisitor() {
												public boolean visit(VariableDeclarationFragment fragment) {
													if (fragment.toString()
															.startsWith(varName + "=OscarProperties.getInstance()")
															|| fragment.toString().startsWith(
																	varName + "=oscar.OscarProperties.getInstance()")) {
														isOscarPropertiesVariable = true;
														if (isOscarPropertiesVariable && DEBUG) {
															console.writeln("Declaration of OscarProperties variable: "
																			+ fragment.toString());
														}
													}
													return true;
												}
											});
										}
										if (isOscarPropertiesVariable) {
											Boolean r = astNodes.add(node);
											if (!r) {
												console.writeln(
														"Unexpected presence of node " + node.getName().toString());
											}
											Boolean b = isBoolean((StringLiteral) node.arguments().get(0));
											if (DEBUG)
												printDebugInfo(cu, node, type, stringLiteral, b, false);
											addProperty(key, b);
										}
									}
								}
							}
						}
					}
					return true;
				}
			});
		}

	}

	/**
	 * Reads a ICompilationUnit and creates the AST DOM for manipulating the
	 * Java source file
	 * 
	 * @param unit
	 * @return
	 */

	private static CompilationUnit parse(ICompilationUnit unit) {
		ASTParser parser = ASTParser.newParser(AST.JLS8);
		parser.setKind(ASTParser.K_COMPILATION_UNIT);
		parser.setSource(unit);
		parser.setResolveBindings(true);
		return (CompilationUnit) parser.createAST(null); // parse
	}

	private void printDebugInfo(CompilationUnit cu, ASTNode node, ITypeBinding type, StringLiteral stringLiteral, Boolean b, Boolean verbose) {
		printDebugInfo(cu, node, type, stringLiteral, b);
		if (verbose) {
			console.writeln("  in parent statement: " + getParentStatement(stringLiteral).toString());
		}
	}

	private void printDebugInfo(CompilationUnit cu, ASTNode node, ITypeBinding type, StringLiteral stringLiteral, Boolean b) {
		console.writeln("Found: " + stringLiteral + " in " + getPackageAndFilename(cu));
		console.writeln("  Node: " + node.toString());
		if (type != null) {
			console.writeln("  of type: " +type.getName());
		} else {
			console.writeln("  of type: null");
		}
		console.writeln("  present in expression: " + getFullExpression(stringLiteral));
		console.writeln("  is Boolean: " + b);
	}


	private String getPackageAndFilename(CompilationUnit cu) {
		return "Package: " + cu.getPackage().getName().getFullyQualifiedName() + ", File: "
				+ cu.getJavaElement().getElementName();
	}

	/**
	 * Gets the surrounding {@link Statement} of this a {@link StringLiteral}
	 * ast node.
	 *
	 * @param reference
	 *            any {@link StringLiteral}
	 * @return the surrounding {@link Statement} as found in the AST
	 *         parent-child hierarchy
	 */
	private Statement getParentStatement(StringLiteral reference) {
		ASTNode node = reference;
		while (!(node instanceof Statement)) {
			node = node.getParent();
			if (node == null)
				break;
		}
		return (Statement) node;
	}

	private Expression getFullExpression(StringLiteral reference) {
		ASTNode node = reference;
		while (node.getParent() instanceof Expression) {
			node = node.getParent();
		}
		return (Expression) node;
	}

	private Boolean isBoolean(StringLiteral reference) {
		Boolean result = false;
		ASTNode node = reference;
		ITypeBinding expressionType;
		while (node.getParent() instanceof Expression) {
			node = node.getParent();
			expressionType = (ITypeBinding) ((Expression) node).resolveTypeBinding();
			if (expressionType != null && expressionType.getQualifiedName() != null
					&& (expressionType.getQualifiedName().contains("Boolean")
							|| expressionType.getQualifiedName().contains("boolean"))) {
				result = true;
				break;
			}
		}
		return result;
	}

	/**
	 * Finds the parent {@link Block} of a {@link Statement}.
	 *
	 * @param s
	 *            the {@link Statement} to find the its parent {@link Block} for
	 * @return the parent block of {@code s}
	 */
	public static Block getParentBlock(Statement s) {
		ASTNode node = s;
		while (!(node instanceof Block)) {
			node = node.getParent();
		}
		return (Block) node;
	}

	public static Block getParentBlock(MethodInvocation s) {
		ASTNode node = s;
		while (!(node instanceof Block)) {
			node = node.getParent();
		}
		return (Block) node;
	}

}
