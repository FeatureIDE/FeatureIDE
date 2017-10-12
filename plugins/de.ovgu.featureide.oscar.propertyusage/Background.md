# Background

Many aspects of the run-time behaviour of OSCAR EMR depend on a stored
set of properties which are read from the filesystem when OSCAR is
started.  There are hundreds of such properties stored as key-value
pairs (for example, "db_name=xxx").

Some OSCAR properties provide information such as "db_user=xxx" and
"db_password=xxx" which are needed to access the OSCAR database.
Other properties are used to determine which run-time code should be
executed.  For instance, "billregion=BC" will cause OSCAR to run the
BC billing code rather than the ON billing code.

Implementation of the MAVIS Variability Model Extraction algorithm
depends on the ability to detect whether or not properties are used in
Boolean expressions.  If a property is used in a Boolean expression
then the property influences the control flow of the software and may
represent a "Variation Point".

Since OSCAR is implemented in Java and the Eclipse Java Development
Tools (JDT) project provides tools to analyze Java source code, it is
natural to consider whether the JDT provides the means to reliably
determine how the Java properties are used.  The Java Model and the
Abstract Syntax Tree (AST) contained in the JDT provide what is needed.

## Java Model


The Java Model defined in the org.eclipse.jdt.core plug-in provides
the means to locate the Eclipse workspace and loop through all the
projects in the workspace.  Those projects that are implemented in
Java are further analyzed.  This is implemented in the findProject()
method within src/propertyusage/handlers/PropertyUsage.java.

Each of the packages within the Java project is examined and if the
package contains Java source code, then an AST can be generated for
each of the source code files contained in that package.  This is done
in the analyseMethods() method within
src/propertyusage/handlers/PropertyUsage.java which calls createAST().

## Abstract Syntax Tree (AST)

The AST provides a detailed tree representation of the Java source
code.  For our purposes we are only interested in reading the source
code but the AST can also be used to create, modify or delete source
code.  The Java source code is represented within the AST by various
subclasses of the ASTNode class.

An AST is created for each file containing Java source code using the
parse() method in src/propertyusage/handlers/PropertyUsage.java.  The
parser is invoked with the option setResolveBindings(true) which
allows us to determine to which class the method belongs and the
return type of the method.

To get information from the AST we use the ASTVisitor class which
implements the Visitor Pattern.  The ASTNode of most interest to use
is the MethodInvocation node but we will also make some us of the
MethodDeclaration and VariableDeclarationFragment AST node types.


# Analyzing the OSCAR source code

## Property Initialization in OSCAR

OSCAR uses the oscar.OscarProperties class which extends the
java.util.Properties parent class to load the OSCAR properties files.
OscarProperties implements the singleton design pattern.  The
OscarProperties constructor is hidden (declared private) and access to
OscarProperties is restricted to OscarProperties.getInstance().  The
OscarProperties constructor loads an initial set of default properties
from the file "oscar_mcmaster.properties".

During OSCAR start up, the single instance of OscarProperties is
updated within oscar.login.Startup with a customized set of Oscar
properties from a file in the home directory of the user running the
Java Servlet Container.  The name of the file with customized
properties is the name of the deployed web application with the
extension ".properties".  For instance, if the deployed web
application is called "oscar15" then the customized properties are
stored in "oscar15.properties".  In a standard OSCAR EMR installation,
this properties file will be in the home directory of 'tomcat7'.

Key-value pairs with the same key can appear multiple times in the
properties files.  The value of the last instance read will be stored
in OscarProperties.  So for instance, if the deployed web application
is called 'oscar', then "billregion=ON" in oscar_mcmaster.properties
will be replaced by "billregion=BC" if that key-value pair exists in
"oscar.properties".  Any key-value pair set in
'oscar_mcmaster.properties' that is not customized will retain the
value set in 'oscar_mcmaster.properties'.

## Property Initialization in the PropertyUsage plugin

As initially envisioned, the PropertyUsage plugin needed to read the
keys stored in the Oscar properties files so that they could be
searched for in the source code.  An easy way to do that was to give
the PropertyUsage plugin its own copy of "OscarProperties.java" and
"Startup.java".

The copy of "OscarProperties.java" in "src/oscar/OscarProperties.java"
is identical to the original except that it sends messages to stdout
rather than Log4j.  Its constructor loads default key-value pairs from
a properties file "src/resources/oscar_mcmaster.properties" which is a
known location with respect to the plugin source code.  This file is
identical to the version in OSCAR EMR which could be anywhere in the
filesystem.  (Relative to the base of the Oscar git repo, it is in
src/main/resources/oscar_mcmaster.properties.)

The copy of "Startup.java" has also been modified to write to stdout
rather than Log4j but has had more extensive modifications to remove
references to the Servlet Context in which it would run within the
OSCAR EMR web environment.  Since the PropertyUsage plugin is not a
deployed web application, the name of the customized properties file
has been set to "oscar.properties" rather than determining it from the
servlet context resource path.

By using "OscarProperties.java" and "Startup.java", we load the
properties in the same manner that they will be loaded in OSCAR EMR.
The file "oscar.properties" is just "oscar_mcmaster.properties"
customized so that all property keys present in the original are
uncommented. That allows the PropertyUsage plugin to know about all
documented key-value pairs present in the "oscar_mcmaster.properties"
file.

# Finding Properties in the Java code

## Dealing with JSP files

The ASTParser provided by the org.eclipse.jdt.core plug-in requires
Java source code.  The Oscar properties are used extensively within
JSP files which cannot be analyzed directly.  At the time this is
being written, there are 1643 JSP files.  Fortunately the 'mvn verify'
phase within the Oscar EMR Maven build compiles the JSP files to Java
source code which it writes to target/generated_jsp_classes.  By
including "target/generated_jsp_classes" within the Eclipse build path
of the Java code under analysis, we are able to find properties
present in the Java code generated from the JSP files.  There are also
54 JSPF (Java Server Page Fragment) files in the source code which are
not compilable to source code.  Nine of the JSPF files contain
relevant Oscar properties.


## Using the OscarProperties class

Examination of the source code quickly reveals that the are a large
number of Oscar properties that are not documented in
"oscar_mcmaster.properties".  For instance, in the method
"isSiteSecured()" in "OscarProperties.java" we find the key
"security_site_control" which is not documented.

So rather than looking for the property keys within the source code as
was initially envisioned, it is better to examine the source code for
usages of the singleton OscarProperties class which must be referenced
anywhere in the Java code where an Oscar property is used.

OscarProperties has declarations for 58 methods at the time this is
being written.  However, the two most commonly invoked methods are
"getProperty(String key)" and "getProperty(String key, String
defaultValue)".  They are not declared in OscarProperties itself but
are inherited from the Properties class.  This presents a minor
obstacle because the AST resolves the bindings of these methods to the
Properties class rather than OscarProperties.

The Java Properties API is used within Oscar for other purposes than
for storing the OscarProperties key-value pairs.  Consequently, a call
to getProperties may not be relevent to OscarProperties.  A simple way
to ensure that the AST resolves the bindings of getProperty() to
OscarProperties, where that is appropriate, is to modify the Oscar
source code under analysis to explictly declare the following two
methods within OscarProperties.java:

       public String getProperty(String key) {
               return super.getProperty(key);
       }

       public String getProperty(String key, String defaultValue) {
               return super.getProperty(key, defaultValue);
       }

By adding these two methods, we make the implicit behaviour explicit.
This does not change the run-time behaviour of the code being analyzed
but it allows the AST to resolve the bindings to OscarProperties when
that is appropriate.  Doing this isn't essential, but it ensures that
Oscar property keys are identified correctly.

By detecting all string literals that appear as the first argument of
an OscarProperties method such as OscarProperties.getProperty(key) we
detect most of the expected Oscar properties as well as many more that
are undocumented.  Detection of these properties is done in our
implementation of the visit(MethodInvocation node) method which is
used by ASTParser when it examines MethodInvocation nodes in the AST.

## Other Means

By inspection of documented properties that are not found as the first
string literal in the arguments of an OscarProperties method call, it
was determined that some additional approaches are needed.

1) The Java Properties class inherits methods from
java.util.Hashtable.  Consequently, it is possible to access an Oscar
property with code like this, found in
src/main/java/org/oscarehr/myoscar/utils/MyOscarLoggedInInfo.java:

String temp=
       (String)OscarProperties.getInstance().get("myoscar_server_base_url");

This case is handled by checking whether the MethodInvocation node has
the SimpleName "get" and is in a node that when expressed as a string
starts with "OscarProperties.getInstance.get(" or
"oscar.OscarProperties.getInstance.get(".  There appears to be only
one instance of using the Hashtable "get" method to retrieve an Oscar
property within the code base.

2) Many Oscar properties are used to determine whether or not jsp code
will be included on a web page.  This is implemented in the
OscarPropertiesCheck class which extends TagSupport.  MethodInvocation
nodes of type OscarPropertiesCheck that contain a StringLiteral, such
as "key", as their first argument are checked to see whether they are
calls to setValue("key"), setDefaultVal("key") or setReverse("key")
indicating that "key" is an Oscar property.  If they are then "key" is
counted as an Oscar property and is assumed to be of type Boolean
based on the intended usage of the OscarPropertiesCheck class.

3) The IsPropertiesOn class, while not extending the OscarProperties
class, uses OscarProperties to determine whether or not an Oscar
property has the (case-insensitive) value of "true", "on" or "yes".
The first string literal argument of any method of this class will be
an Oscar property of type Boolean.

4) There are quite a few instances where JSP code uses the
IsModuleLoadTag class which extends TagSupport to determine whether a
module is loaded.  Internally, IsModuleLoadTag references
OscarProperties.getInstance().  All IsModuleLoadTag method invocations
use the setModuleName(String) method to specify the module that is
being checked.  Any string literal argument to this method will be an
Oscar property and is assumed to be of type Boolean.

5) The final check is to examine MethodInvocation nodes of return type
Properties.  There are many instances of code like:

	     Properties p = OscarProperties.getInstance();
	     [...]
	     p.getProperty("key");

Even when we add explicit getProperty() methods to OscarProperties, this
usage bypasses those methods, calling the Properties getProperty()
method.

The ASTParser knows that p is of type Properties but we need to know
whether it contains Oscar properties.  There are many usages of the
Properties API that do not relate to Oscar properties.  To determine
whether "p", or whatever the variable is named, is an Oscar property,
we need to examine its declaration.  This is done by declaring a new
ASTVisitor() to visit VariableDeclarationFrament nodes of the current
compilation unit.  If a declaration of the form
"p=OscarProperties.getInstance()" or
"p=oscar.OscarProperties.getInstance()" exists then p is assumed to be
an Oscar properties variable and "key" is counted as an Oscar
property.

This same branch of code can also deal with OscarProperties not having
explicit getProperty methods.  (This part of the code is not reached,
however, if OscarProperties does have explicit getProperty methods.)
To do that it first checks whether the method invocation node is in
the oscar.OscarProperties.java compilation unit.  If so the first
string literal argument of any such method is an Oscar property.  It
then examines the prefix to calls to getProperty().  If the prefix
contains the string "OscarProperties.getInstance()" then the first
string literal argument is an Oscar property key.  (This code gives
nearly identical results to those obtained when augmenting
OscarProperties.java with the two getProperty methods.)

# What More Could Be Done

The PropertyUsage plugin looks for keys that are present in the first
argument of an OscarProperties method in the form of a literal string.
If the first argument isn't a literal string it is ignored.  That
means that a variable containing a key will not be detected. For
instance, as implemented the key "billregion" would not be detected in
the following code:

     String billregion="billregion";
     oscar.OscarProperties.getProperty(billregion);

The plugin could be extended to handle such cases.  However, they are
not common.  Only a handful of documented keys that are not detected
can be found as strings in Java source files.  A Python utility script
"findProperties.py" was written to walk through the entire Oscar
repository looking for undetected strings.

There are also a few keys like "confidentiality_statement.v1" and
"confidentiality_statement.v2" used in the expression

	statement = oscarProperties.getProperty("confidentiality_statement.v" + count))

from oscar.OscarProperties.java that not be detected.  Usage of this
sort which generates a unlimited number of potential keys on the fly
is difficult to detect.

The JSPF files are not analyzed by the ASTParser unless their body is
included within a JSP file.  Some are not included.  Nine of them are
known to include documented Oscar properties.  The JSPF file
src/main/webapp/provider/caseload.jspf contains the undetected boolean
key CASELOAD_DEFAULT_ALL_PROVIDERS.

Other documented but missing properties can be found in xml files
like:

      src/main/resources/applicationContextBORN18M.xml
      src/main/resources/applicationContextBORN.xml
      src/main/resources/applicationContextCBI.xml
      src/main/resources/applicationContext.xml
      src/main/resources/spring_hibernate.xml
      src/main/resources/spring_jpa.xml

They are used in the configuration of JavaBeans within the Spring
framework.  These JavaBeans are available at run time but do not exist
as compilable Java code that can be analyzed by the AST.

