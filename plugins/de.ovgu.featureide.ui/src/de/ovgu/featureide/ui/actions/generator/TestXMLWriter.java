package de.ovgu.featureide.ui.actions.generator;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.nio.charset.Charset;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class TestXMLWriter implements XMLCoverage {

	private TestResults testResults;

	public TestXMLWriter(TestResults testResults) {
		this.testResults = testResults;
	}

	public String write() throws ParserConfigurationException, TransformerException {
		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		dbf.setNamespaceAware(true);
		dbf.setIgnoringComments(true);
		dbf.setIgnoringElementContentWhitespace(false);
		dbf.setCoalescing(true);
		dbf.setExpandEntityReferences(true);
		DocumentBuilder db = dbf.newDocumentBuilder();
		Document doc = db.newDocument();
		// Create the Xml Representation
		return createXMLDocument(doc);
	}

	private String createXMLDocument(Document doc) throws TransformerException {
		Element root = doc.createElement("testrun");
		root.setAttribute("ignored", Integer.valueOf(testResults.ignored).toString());
		root.setAttribute("errors", Integer.valueOf(testResults.errors).toString());
		root.setAttribute("started", Integer.valueOf(testResults.started).toString());
		root.setAttribute("tests", Integer.valueOf(testResults.tests).toString());
		root.setAttribute("project", testResults.project);
		root.setAttribute("name", testResults.name);

		for (Entry<String, Map<String, Set<Test>>> result : testResults.testResults.entrySet()) {
			Element suite = doc.createElement("testsuite");
			suite.setAttribute("name", result.getKey());
			float suiteTime = 0;
			for (Entry<String, Set<Test>> configTest : result.getValue().entrySet()) {
				Element config1 = doc.createElement("testsuite");
				config1.setAttribute("name", configTest.getKey());
				float configTime = 0;
				for (Test test : configTest.getValue()) {
					Element testCase = doc.createElement("testcase");
					testCase.setAttribute("name", test.name);
					testCase.setAttribute("classname", test.classname);
					testCase.setAttribute("time", test.time + "");
					if (test.failure != null) {
						Element failure;
						if (test.failure.getException() instanceof AssertionError) {
							failure = doc.createElement("failure");
						} else {
							failure = doc.createElement("error");
						}
						failure.setTextContent(test.failure.getTrace());
						testCase.appendChild(failure);
					}
					config1.appendChild(testCase);
					configTime += test.time;
				}
				suiteTime += configTime;
				config1.setAttribute("time", Double.valueOf(configTime).toString());
				suite.appendChild(config1);
			}
			suite.setAttribute("time", Double.valueOf(suiteTime).toString());
			root.appendChild(suite);
		}
		doc.appendChild(root);

		// Transform the Xml Representation into a String
		Transformer transfo = TransformerFactory.newInstance().newTransformer();
		transfo.setOutputProperty(OutputKeys.METHOD, "xml");
		transfo.setOutputProperty(OutputKeys.INDENT, "yes");
		StreamResult result = new StreamResult(new StringWriter());
		DOMSource source = new DOMSource(doc);
		transfo.transform(source, result);
		return prettyPrint(result.getWriter().toString());
	}

	public void writeToFile(File file) throws ParserConfigurationException, TransformerException {
		try (FileOutputStream output = new FileOutputStream(file)) {
			if (!file.exists()) {
				file.createNewFile();
			}
			output.write(write().getBytes(Charset.availableCharsets().get("UTF-8")));
			output.flush();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Inserts indentations into the text
	 * 
	 * @param text
	 * @return
	 */
	private String prettyPrint(String text) {
		StringBuilder result = new StringBuilder();
		String line;
		int indentLevel = 0;
		BufferedReader reader = new BufferedReader(new StringReader(text));
		try {
			line = reader.readLine();
			while (line != null) {
				if (line.startsWith("</")) {
					indentLevel--;
					for (int i = 0; i < indentLevel; i++) {
						result.append("\t");
					}
				}

				else if (line.startsWith("<")) {
					for (int i = 0; i < indentLevel; i++) {
						result.append("\t");
					}
					if (!line.contains("</")) {
						indentLevel++;
					}
				} else {
					for (int i = 0; i < indentLevel; i++) {
						result.append("\t");
					}
				}
				result.append(line + "\n");
				if (line.contains("/>")) {
					indentLevel--;
				}
				line = reader.readLine();
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		return result.toString();
	}

}
