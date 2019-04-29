# Example Plug-In

## Description
This Plug-In enables users to import example projects into their workspace.
It contains all example projects of FeatureIDE and features an GUI wizard for importing.

## Developer Information

### How to add a new example project
1. Copy the project folder of the example in the folder `featureide_example`
2. Remove unnecessary files in the project (e.g., bin files)
3. Run the launch file `UpdateIndexFiles.launch`
4. Refresh the folder `featureide_example` _(Optional)_
5. Modify the newly created file `projectInformation.xml` in the folder of the example project _(Optional)_

### How to rebuild the list of example projects
1. Remove unnecessary files in **every** example project (e.g., bin files)
2. Run the launch file `UpdateIndexFiles_Force.launch`
3. Refresh the folder `featureide_example` _(Optional)_
