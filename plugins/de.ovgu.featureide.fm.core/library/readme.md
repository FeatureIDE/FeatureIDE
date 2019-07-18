# How to build the fm.core library

## Before Build
 - Create the file `build_jar.properties` by copying the file `build_jar_template.properties`.
 - Then adapted the variable `bin.javac.path` in `build_jar.properties` such that it points to a suitable Java compiler (javac).

## Build
 - **Using the command line:**
  - Run *ant* with the target *build* (or *clean_build*).
 - **Using Eclipse:**
  - Execute the file `fm.core.lib-Build.launch` ("Run As" in the Eclipse context menu).
  - For a clean build (deleting old build folder before compiling) execute `fm.core.lib-Clean_Build.launch`.

 - The result should be a jar file named `de.ovgu.featureide.lib.fm.core.jar` (in the folder `library/jar` of the fm.core project).
	
 - Please pay attention to the console output.

## What could may wrong
 - No JDK is installed:	
  - In order for this to work a path to a suitable Java compiler must be set.
	The script `subant_build_jar.xml` specifies a default value for Windows and OpenJDK.
	This value can be modified by setting a value to the variable `bin.javac.path` in the file `build_jar.properties`.
	This file is ignored by *git*, so it must be created by hand, if it is not already there.
	The file `build_jar_template.properties` can be used as a template for this purpose.
 - Due to changes there are unwanted dependencies (e.g., to Eclipse API) in the source files:
  - In the build script some files are explicitly excluded from the build process.
	These files contain dependencies to the Eclipse API (or are deprecated).
	If other files contain such dependencies it build process fails (with a lot of confusing complier errors).
	In this case either fix the dependency problem or, if not possible, add the file to the exclude list (`excluded_source_files.txt`).
  - Since the complier errors from the build process are not helpful for this problem and do not point you the respective file, there is a quick and dirty method to detect the dependency problem.
	Make a local copy of the src folder or make sure all files in it are committed to your git repository.
	Then run the script `subant_build_jar.xml` with the target *deleteFiles*.
	It now deletes all files that are excluded from the build process.
	If there is no problem then the remaining files are compilable without any errors.
	Otherwise, the real problem should be easy to spot.
	After fixing the problem, restore the delete files from git or your local copy.

