How to build the fm.core library.

Build:
	Execute the file fm.core.lib-Build.launch ("Run As" in the context menu).
	It should also appear as external tool, which you can execute.
	(Alternatively you can also execute the build.xml as ant script. However the other method is recommended for Eclipse users.)
	For a clean build (deleting old build folder before compiling) execute fm.core.lib-Clean_Build.launch.
	
	The end result should be a jar file named de.ovgu.featureide.lib.fm.jar (in the folder library/jar of the fm.core project).
	
	Please pay attention to the console output.

What could go wrong:
	No JDK is installed:	
		In order for this to work you need the JAVA_HOME variable on your system to point to a JDK with the java compiler.
		It must be Java 1.7 or higher.
	
	
	Due to changes there are unwanted dependencies (e.g., to Eclipse API) in the source files:
		In the build script some files are explicitly excluded from the build process.
		These files contain dependencies to the Eclipse API (or are deprecated).
		If other files contain such dependencies it build process fails (with a lot of confusing complier errors).
		In this case either fix the dependency problem or, if not possible, add the file to the exclude list (excluded_source_files.txt).
		
		Since the complier errors from the build process are not helpful for this problem and do not point you the respective file, there is a quick'n'dirty method to detect the dependency problem.
		Make a local copy of the src folder or make sure all files in it are committed to your git repository.
		Then run the script subant_build_jar.xml with the target "deleteFiles".
		It now deletes all files that are excluded from the build process.
		If there is no problem then the remaining files are compilable without any errors.
		Otherwise, the real problem should be easy to spot.
		After fixing the problem, restore the delete files from git or your local copy.

