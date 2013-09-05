package br.ufal.ic.colligens.models;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.jdom2.Document;
import org.jdom2.Element;
import org.jdom2.JDOMException;
import org.jdom2.input.SAXBuilder;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.util.Log;

/**
 * @author Thiago Emmanuel
 * 
 */
public class XMLParserTypeChef {
	private SAXBuilder builder;
	private File xmlFile;
	private FileProxy fileProxie;

	public XMLParserTypeChef() {
		builder = new SAXBuilder();
	}

	/**
	 * @param fileProxie
	 */
	public void setFile(FileProxy fileProxie) {
		this.fileProxie = fileProxie;
	}

	/**
	 * @param xmlFile
	 */
	public void setXMLFile(File xmlFile) {
		this.xmlFile = xmlFile != null ? xmlFile : this.xmlFile;
	}

	public void processFile() {
		if (xmlFile == null) {
			xmlFile = new File(Colligens.getDefault().getConfigDir()
					.getAbsolutePath()
					+ System.getProperty("file.separator") + "output.xml");
			if (!xmlFile.exists())
				return;
		}
		try {
			Document document = builder.build(xmlFile);
			Element rootNode = document.getRootElement();

			TypeErroProcessFile(rootNode, "typeerror");
			TypeErroProcessFile(rootNode, "parsererror");

		} catch (IOException io) {
			System.out.println(io.getMessage());
		} catch (JDOMException jdomex) {
			System.out.println(jdomex.getMessage());
		}
	}

	private void TypeErroProcessFile(Element rootNode, String type) {

		List<Element> list = rootNode.getChildren(type);

		for (int i = 0; i < list.size(); i++) {
			Element node = list.get(i);

			String file = node.getChild("position").getChildText("file").trim();

			// compare with the log file that was analyzed
			if (file.contains(fileProxie.getFileToAnalyse())) {

				Log log = new Log(fileProxie, node.getChild("position")
						.getChildText("line"), node.getChildText("featurestr"),
						node.getChildText("severity"), node.getChildText("msg"));
				
				fileProxie.getLogs().add(log);

			}
		}

	}

}
