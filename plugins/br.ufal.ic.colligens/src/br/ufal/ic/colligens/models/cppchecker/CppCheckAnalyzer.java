package br.ufal.ic.colligens.models.cppchecker;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.jdom2.Document;
import org.jdom2.Element;
import org.jdom2.JDOMException;
import org.jdom2.input.SAXBuilder;

public class CppCheckAnalyzer {
	private final HashMap<String, CppCheckerFileLogs> hashMap;

	public CppCheckAnalyzer() {
		hashMap = new HashMap<String, CppCheckerFileLogs>();
	}

	public void processFile(IFile iFile) {
		CppChecker checker = new CppChecker();

		checker.checkFile(iFile.getLocation().toFile(), iFile.getProject()
				.getName());

		String xml = checker.getXmlFile();

		// System.err.println(xml);

		SAXBuilder builder = new SAXBuilder();
		Reader in = new StringReader(xml);
		Document doc = null;
		// Element root = null;
		// Element meta = null;
		// Element _code = null;
		// Element _description = null;

		// @SuppressWarnings("unused")
		// String code = null;
		// @SuppressWarnings("unused")
		// String description = "";

		try {
			doc = builder.build(in);
			// TODO xml não contem "commResponse"
			//
			// root = doc.getRootElement();
			// meta = root.getChild("commResponse").getChild("meta");
			// _code = meta.getChild("code");
			// _description = meta.getChild("description");
			// code = _code.getText();
			// description = _description.getText();

		} catch (JDOMException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}

		Element rootNode = doc.getRootElement();

		List<Element> list = rootNode.getChildren();

		for (Iterator<Element> i = list.iterator(); i.hasNext();) {

			Element element = i.next();

			String file = element.getAttributeValue("file");
			file = file.substring(iFile.getProject().getLocation().toOSString()
					.length(), file.length());

			CppCheckerFileLogs fileLogs = null;
			if (hashMap.containsKey(file)) {
				fileLogs = hashMap.get(file);
			} else {
				fileLogs = new CppCheckerFileLogs(iFile.getProject().getFile(
						file));
				hashMap.put(file, fileLogs);
			}

			CppCheckerLog log = new CppCheckerLog(fileLogs,
					element.getAttributeValue("line"),
					element.getAttributeValue("id"),
					element.getAttributeValue("severity"),
					element.getAttributeValue("msg"),
					element.getAttributeValue("config"));

			fileLogs.addLog(log);

		}

	}

	public List<CppCheckerFileLogs> getFiles() {
		List<CppCheckerFileLogs> list = new LinkedList<CppCheckerFileLogs>();

		Collection<CppCheckerFileLogs> collection = hashMap.values();

		for (Iterator<CppCheckerFileLogs> iterator = collection.iterator(); iterator
				.hasNext();) {
			CppCheckerFileLogs fileLogs = iterator.next();
			list.add(fileLogs);
		}

		return list;

	}

}
