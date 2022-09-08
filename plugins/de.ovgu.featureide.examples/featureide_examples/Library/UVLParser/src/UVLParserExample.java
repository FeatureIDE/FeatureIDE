import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.vill.config.Configuration;
import de.vill.main.UVLModelFactory;
import de.vill.model.Attribute;
import de.vill.model.Feature;
import de.vill.model.FeatureModel;
import de.vill.model.Group;
import de.vill.model.constraint.Constraint;

public class UVLParserExample {
	public static void main(String[] args) throws IOException {
		FeatureModel featureModel = loadUVLFeatureModelFromFile("server.uvl");

		// Print features
		Set<String> featureNames = featureModel.getFeatureMap().keySet();
		System.out.println("Features:" + featureNames.toString());
		
		// Print constraints
		List<Constraint> constraints = featureModel.getConstraints();
		for (Constraint constraint : constraints) {
			System.out.println("Constraint: " + constraint);
		}
		
		// Read attribute values
		System.out.println("Required memory to store windows: " + getAttributeValue(featureModel, "Windows", "Memory"));
		
		
		// Save UVL feature model
		writeUVLFeatureModelToFile(featureModel, "output_model.uvl");

		// Load decomposed feature model
		FeatureModel composedModel = loadUVLFeatureModelFromDirectory("decomposed.uvl");
		
		printImportedFeatureTrees(composedModel.getRootFeature());
		
		// Compose and write feature model
		writeComposedUVLFeatureModelToFile(composedModel, "output_composedModel.uvl");
		
		
	}

	/**
	 * Parse uvl model from file (if decomposed all submodels must be in the current
	 * working directory)
	 * 
	 * @param path path to the file with uvl model
	 * @return the uvl model described in the file
	 * @throws IOException for io exceptions while loading the file content
	 */
	private static FeatureModel loadUVLFeatureModelFromFile(String path) throws IOException {
		Path filePath = Paths.get(path);
		String content = new String(Files.readAllBytes(filePath));
		UVLModelFactory uvlModelFactory = new UVLModelFactory();
		FeatureModel featureModel = uvlModelFactory.parse(content);
		return featureModel;
	}

	/**
	 * Parse a decomposed uvl model where all submodels are in a directory and named
	 * according to their namespaces.
	 * 
	 * @param rootModelPath Path to the uvl root model file
	 * @param subModelDir   Path to the directory with all submodels
	 * @return the uvl model described in the file
	 * @throws IOException for io exceptions while loading the file content
	 */
	private static FeatureModel loadUVLFeatureModelFromDirectory(String rootModelPath)
			throws IOException {
		Path filePath = Paths.get(rootModelPath);
		String content = new String(Files.readAllBytes(filePath));
		UVLModelFactory uvlModelFactory = new UVLModelFactory();
		FeatureModel featureModel = uvlModelFactory.parse(content, "./");
		return featureModel;
	}
	
	
	/**
	 * Parse a decomposed uvl model where all submodels locations are specified in a
	 * map with namespace as key and path as value.
	 * 
	 * @param rootModelPath Path to the uvl root model file
	 * @param subModelPaths Map with submodels with namespace as key and path as
	 *                      value
	 * @return the uvl model described in the file
	 * @throws IOException for io exceptions while loading the file content
	 */
	private static FeatureModel loadUVLFeatureModelWithSpecificPaths(String rootModelPath,
			Map<String, String> subModelPaths) throws IOException {
		Path filePath = Paths.get(rootModelPath);
		String content = new String(Files.readAllBytes(filePath));
		UVLModelFactory uvlModelFactory = new UVLModelFactory();
		FeatureModel featureModel = uvlModelFactory.parse(content, subModelPaths);
		return featureModel;
	}
	
	private static void writeUVLFeatureModelToFile(FeatureModel featureModel, String path) throws IOException {
		// change newline and tabulator symbol for printing
		Configuration.setTabulatorSymbol("        ");
		Configuration.setNewlineSymbol("\n");

		// safe a single uvl model (this ignores any submodels)
		String uvlModel = featureModel.toString();
		Path filePath = Paths.get(path);
		Files.write(filePath, uvlModel.getBytes());
	}
	
	private static void writeDecomposedUVLFeatureModelToFile(String path, FeatureModel featureModel) throws IOException {
		// safe a decomposed uvl model with all its submodels to individual files
		Map<String, String> modelList = featureModel.decomposedModelToString();
		for (Map.Entry<String, String> uvlSubModel : modelList.entrySet()) {
			// safe submodel in sub directory directory with namespace as name
			Files.createDirectory(Paths.get("./subModels/"));
			Path filePath = Paths.get("./subModels/" + uvlSubModel.getKey() + ".uvl");
			Files.write(filePath, uvlSubModel.getValue().getBytes());
		}
	}
	
	private static void writeComposedUVLFeatureModelToFile(FeatureModel featureModel, String path) throws IOException {
		String uvlModel = featureModel.composedModelToString();
		Path filePath = Paths.get(path);
		Files.write(filePath, uvlModel.getBytes());
	}
	
	private static void printImportedFeatureTrees(Feature parent) {
		for (Group childGroup : parent.getChildren()) {
			for (Feature child : childGroup.getFeatures()) {
				if (child.isSubmodelRoot()) {
					System.out.println("Imported Submodel:" + child.getFeatureName());
				}
			}
		}
	}

	
	public static Object getAttributeValue(FeatureModel featureModel, String featureName, String attributeName) {
		// get attribute from feature
		Feature feature = featureModel.getFeatureMap().get(featureName);
		String value = "";
		if (feature != null) {
			Attribute attribute = feature.getAttributes().get(attributeName);
			if (attribute != null) {
				value = attribute.getValue().toString();
			} else {
				System.err.println("Attribute " + attributeName + " in feature " + featureName + " not found!");
			}
		} else {
			System.err.println("Feature " + featureName + " not found!");
		}
		
		return value;
	}
}
