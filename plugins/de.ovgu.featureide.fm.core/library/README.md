# FeatureIDE fm.core library

## Install

### Download
- Download source files from git  
`git clone https://github.com/FeatureIDE/FeatureIDE.git`  
`cd FeatureIDE`  
`git checkout release3.6`  

- For experimental functions, you might want to checkout *develop* or a different branch

### Build
- Go to the folder `library` of the fm.core plug-in  
`cd plugins/de.ovgu.featureide.fm.core/library`
- Compile the source
  - **Using the command line:**
    - Run *ant* with the target *build* (or *clean_build*)  
	`ant build`  
	
  - **Using Eclipse:**
    - Execute the file `fm.core.lib-Build.launch` ("Run As" in the Eclipse context menu).
    - For a clean build (deleting old build folder before compiling) execute `fm.core.lib-Clean_Build.launch`.

- Ant creates two folders
  - `bin` contains all generated class files
  - `jar` contains the executable jar file and a folder `lib` containing all required libraries
	
 - Please pay attention to the console output.

### Known Issues
- No JDK is installed:	
  - In order for this to work a path to a suitable Java compiler must be set. You can either add you JDK folder to the *PATH* variable, set the *JAVA_HOME* variable to your JDK folder, or modify the `subant_build_jar.xml` to set a concrete executable for javac.
   
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


## Execute
- Run the jar file an specify your desired command and arguments  
`java -jar de.ovgu.featureide.lib.fm.core.jar <command> [arguments]`

### Currently Available Commands
- *genconfig*
  - Generates a list of configurations using a specified algorithm
  - Example:  
  `java -jar de.ovgu.featureide.lib.fm.core.jar genconfig -a YASA -t 2 -fm model.xml -o sample.csv`  

  - Supported algorithms:
    - YASA
    - IncLing
    - Chvatal
    - ICPL
	- Random
	- All

  - Output format
  	- semicolon-separated values
    - First line (header): "Configuration", Feature names
    - Following lines: Configuration ID, feature selections (0 deselected, 1 selected)

### Supported Input Formats
- FeatureIDE XML
- SXFM
- Dimacs
- GUIDSL
- Velvet
